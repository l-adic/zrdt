# The zrdt git endpoint, version 1

Status: spec for M1, 2026-11-02. The desktop (the fork's git manager) serves it; `git-remote-zrdt`
and `git zrdt` are its clients; `fake/fake_endpoint.py` implements it for tests. It is the narrow
local API between git and the desktop: **git work stays in the helper, zrdt work stays in the
desktop.** The desktop maps these calls onto its zrdt plumbing (app channels, piece stores,
`GIT_PREPARE`, `GIT_OBJECTS`, `GIT_VIEW` in `zrdtd`; BUILD_M1 §4, §5). The helper never sees a
record opening, a nonce, a CDN pointer or a `SERVE` request, and cannot share without the
desktop's own dialog.

## 1. Transport, discovery, authentication

- **HTTP/1.1, JSON bodies** (UTF-8). One request per connection is fine.
- **Where:** loopback TCP, `http://127.0.0.1:<port>`, or HTTP over a Unix stream socket,
  `unix:<path>` (BUILD_M1 §5's `<userData>/zrdt-apps.sock`, mode 0600). A client refuses any
  other host. (BUILD_M1 §5 sketched JSON lines on that socket; this spec puts HTTP on it, so the
  same client works over TCP and the socket.)
- **Discovery**, first match wins: `ZRDT_ENDPOINT`, then `git config zrdt.endpoint`. Each demo
  desktop has its own endpoint, so each clone can carry its own setting.
- **Token**, first match wins: `ZRDT_TOKEN`, `git config zrdt.token`, the file named by
  `ZRDT_TOKEN_FILE` or `git config zrdt.tokenFile` (BUILD_M1: `<userData>/zrdt-apps-git.token`,
  mode 0600). Sent as `Authorization: Bearer <token>`. The token belongs to the git app on one
  desktop, so it names the member; no request names the caller.
- **Scope:** a token sees only `git-sha256` channels of groups its member belongs to. A group the
  member is not in answers exactly like a group that does not exist (404 `no_group`).
- Clients send `X-Zrdt-Protocol: 1`.

## 2. Encodings

| Thing | Encoding |
|---|---|
| object id (`oid`) | 64 lowercase hex: SHA-256 of the raw object, the id in a SHA-256 repository |
| record digest | 64 lowercase hex |
| raw object | `"<type> <decimal length>\0<content>"`, type `commit`, `tree` or `blob`; the length has no leading zero |
| bytes in JSON | standard base64 with padding |
| ref name | `refs/heads/*` or `refs/tags/*`, passing `validRefName` (GIT_PLAN §2.3; no `.zrdt-`, no `refs/zrdt/`, no `refs/notes/` in M1) |
| update | `{"name": ref, "old": [oid…], "new": oid or null, "forced": bool}` |

**An update.** `old` is the list of values the pusher saw for `name` and replaces, sorted, distinct:
empty for a create, several when it merges concurrent values. `new` null is a delete. `forced`
means some `old` value is not an ancestor of `new` (the helper refuses that without `+`/`--force`).
`old` makes supersession explicit (G-M2): a push replaces only what it names, so a concurrent push
stays visible.
*Open issue for the Lean lane:* BUILD_M1 §4.2's body has one `old` per update. The desktop must
encode a list (one update per old value, same name and new), or the body grows a list.

**The object stream.** A push's objects, as raw objects back to back, sorted by id, no repeats
(BUILD_M1 §4.1). It is what the piece store carries; zrdtd recomputes every id from it.

**URL path.** `/v1/git/<group>/<repo>`, both percent-encoded. `group` is the alias the desktop
resolves to a Signal group (1-64 bytes, no `/`, no control character, no outer space); `repo` is
1-64 of `A-Za-z0-9._-`, not starting with `.` or `-`. A git URL is `zrdt::<group>/<repo>`.

## 3. Errors

A call that fails answers non-2xx with `{"error": code, "message": text}`:
400 `bad_request` (malformed JSON, ids, names), 401 `unauthorized`, 404 `no_group`, `no_upload`
or `not_found`, 405 `bad_method`, 413 `too_large`, 400 `bad_piece`, 500 `internal`,
503 `not_running` (Signal is not linked or not running). A push that the zrdt checks refuse is not
an error: it answers **409** with `{"status": "refused", …}` (§4.5).

## 4. Calls

### 4.1 `GET /v1/hello`

```json
{"protocol": 1, "app": "git-sha256", "objectFormat": "sha256", "member": "alice",
 "pieceSize": 1048576, "maxStream": 67108864, "maxObjectsPerRequest": 256}
```

`member` is a display name for messages only. `maxStream` bounds one push's object stream (M1:
64 MiB; chains are deferred). A client refuses any `protocol` other than its own.

### 4.2 `GET /v1/git/<group>/<repo>`: the repository as this member holds it

```json
{"group": "Code", "repo": "demo",
 "members": [{"member": "alice", "self": true}, {"member": "bob", "self": false}],
 "heads": ["<digest>"], "compareCode": "04a48-3d92e-…",
 "records": [Record, …],
 "notGiven": 3,
 "pending": [{"record": "<digest>", "missingPieces": 2}],
 "refs": [{"name": "refs/heads/main",
           "values": [{"value": "<oid>", "record": "<digest>", "forced": false, "author": "bob"}]}]}
```

- `records`: the **applied** push records whose opening this member holds (its table), oldest
  first. A record whose pieces are not all checked yet is in `pending`, not here.
- `Record`: `{"record", "seq", "author", "provenance" ("self" | "live" | "relayed"), "share",
  "links": [digest…], "objects": [oid…], "covers": [member…], "updates": [update…]}`. `seq` is
  this desktop's arrival order, for display. `objects` is exactly the record's object list.
  The **push log** is every update of every record.
- `notGiven`: records of this channel held as structure only (boundary or `after` entries, JOIN
  §6): content this member was not given. Nothing else about them is reported.
- `refs`: the register (BUILD_M1 §4.4, `GIT_VIEW`), over `records`: an assignment (d, n := v) is
  live unless a record e in `records` assigns n with v in its `old` and d is reachable from e's
  links. A delete is replaced by any later assignment of its name. Names whose live values are all
  deletes are omitted, and delete values are not listed.
- `heads`, `compareCode`: the channel's heads and JOIN's compare code over them.
- A channel with no record at all answers with empty lists (no 404), so a typo and a new repo
  look the same until `create` (§4.5).

### 4.3 `POST /v1/git/<group>/<repo>/uploads`: hand over an object stream

Request `{"size": L}` with 1 ≤ L ≤ `maxStream`. Reply (201)
`{"upload": "<id>", "pieceSize": P, "pieces": N}` with N = ⌈L / P⌉. Then, for each i < N:

`PUT /v1/git/<group>/<repo>/uploads/<id>/pieces/<i>` with
`{"sha256": "<hex of the piece>", "data": "<base64>"}`; piece i is bytes [iP, min((i+1)P, L)).
Reply `{"ok": true}`. A piece of the wrong length or hash is refused (400 `bad_piece`); re-sending
a piece replaces it. Uploads are private to the token, are consumed by a published push, and
expire after an hour. This is a local hand-over only: nothing reaches Signal or the CDN until a
push passes its checks (§4.5).

### 4.4 `POST /v1/git/<group>/<repo>/objects`: fetch objects by id

Request `{"ids": [oid…]}`, at most `maxObjectsPerRequest`. Reply
`{"objects": [{"id": "<oid>", "raw": "<base64 raw object>"}], "missing": [oid…]}`.

An object is returned **only if a record in this member's `records` carries it**; every other id
is `missing`, whether or not the channel holds it elsewhere (no existence oracle, no
content-addressed pull of older history). The client recomputes SHA-256(raw) for every object and
refuses the whole fetch on a mismatch.

### 4.5 `POST /v1/git/<group>/<repo>/pushes`: publish a push record

```json
{"upload": "<id>" | null, "objects": [oid…], "updates": [update…],
 "share": false, "covers": null | [member…], "create": false, "dryRun": false}
```

- `objects`: the record's object list, strictly increasing. With objects, `upload` names a
  complete upload whose stream is exactly these objects; with none, `upload` is null (a pure ref
  move or delete).
- `create`: allowed to start a channel that holds no record (`-o zrdt.create`).
- `share`: a deliberate share (from `git zrdt share`); `covers` is the list the user confirmed
  (null asks for it).
- `dryRun`: run every check, publish nothing.

The desktop runs, in order (BUILD_M1 §4.3, over the pusher's own table, i.e. its `records`):

| Reason | When |
|---|---|
| `BAD_OBJECTS` | the stream is not exactly `objects`, is unsorted, or has a tag, a gitlink, a malformed tree, or a commit header outside tree, parent*, author, committer, encoding (no signatures) |
| `BAD_REF` | a name fails `validRefName`; no updates; more than 64 |
| `NEEDS_CREATE` | the channel holds no record and `create` is false |
| `ROOT` | not a share, the channel holds any record or boundary digest, and a carried commit has no parent (G-F1). `objects`: the root commits |
| `OLD_OBJECT` | not a share, and a carried object is in the table (freshness, G-M6). `objects`: those ids. The helper retries once without them; they become references |
| `GATE` | not a share, and some other seated member (non-zero tag) is not entitled to everything the push references but does not carry, or is not seated in a record that assigned `name := v` for an `old` value v (the name rule). `seats`: `[{"member", "reason": "NEW" \| "KEY_CHANGED", "missing": n, "names": [ref…]}]` |
| `BAD_SHARE` | a share whose carried commits are not exactly its updates' new values, that lacks part of their trees, deletes, or has an `old` value other than `new` |
| `KEY_CHANGED` | a share would cover a member whose key changed. `seats` as for `GATE` |
| `COVERS_CHANGED` | a share whose `covers` is null or differs from the members it actually covers (other seated members lacking some carried object the table holds). `covers`: the actual list |
| `DECLINED` | the user declined the desktop's own share dialog |

Reply on success (200):
`{"status": "ok", "record": "<digest>" | null (dry run), "audience": [member…], "covers": [member…]}`.
`ok` means checked, frozen and handed to Signal: published, not "won a race". On refusal (409):
`{"status": "refused", "reason": R, "message": text, …}` with the fields above, and **nothing
was sent**: the desktop checks before any CDN upload, and checks again at freeze with the frozen
audience.

Host duties the endpoint adds to BUILD_M1 §8: answer only on loopback or the 0600 socket; show the
share dialog itself for every `share: true` request (the `covers` sent by the client is the list
the user confirmed in `git zrdt share`, not a substitute for the dialog); never report anything
about records outside `records` beyond the `notGiven` count.

## 5. Test-only calls (fake endpoint)

`fake/fake_endpoint.py` adds, under the admin token: `POST /fake/members {"group", "member",
"token"?}` (add a member), `POST /fake/remove {"group", "member"}`, `POST /fake/key {"member"}`
(change a member's identity key tag), `POST /fake/tamper {"group", "repo", "id"}` (flip, or flip
back, the last byte of a stored object), `GET /fake/dump`. They are not part of the desktop API.
