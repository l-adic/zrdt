# BUILD_M1: apps milestone 1, the mock-server MVP (torrent and git)

Status: build plan, final, 2026-11-02. Branch `apps` in both repos: zrdt from `main` 22c65a3
(protocol 4); the fork (l-adic/signal-desktop-zrdt) from `zrdt` 3eae9af. This plan applies the
user decisions below to [TRANSPORT](TRANSPORT.md), [TORRENT_PLAN](TORRENT_PLAN.md) and
[GIT_PLAN](GIT_PLAN.md), and overrides them where they disagree. The skeleton commit on `apps`
already holds the shared types and the empty, marked lane sections (§D.2). Once a lane's code
lands, its section of the header of `core/Zrdt/Proto.lean` becomes authoritative for its byte
layouts. Until then, §B of this plan is the reference.

**User decisions (2026-11-02).**
- **Scope.** Build both apps. M1 is a mock-server MVP: the Lean core with proofs (stage 1), then
  the fork plumbing and one demo beat per app on Signal's mock server (stage 2). Official servers
  come later.
- **Bulk data.** Both apps move bulk data as **piece stores**. A piece record's opening holds its
  bytes, and a manifest record links all pieces. Privacy comes from the unchanged, proved
  `serve_content`.
- **Git.** Pushes block until a member deliberately shares the repository with a newcomer.
  Repositories use the SHA-256 object format only. Objects travel in raw canonical form,
  `"<type> <len>\0<content>"`, so `zrdtd` recomputes every id and needs no zlib.
- **Branches.** One branch `apps` per repo. Lanes fan out in parallel (§D).

## 0. M1 in one screen

- **Base.**
  - App records are channel records. A channel is a plain zrdt store whose group is a channel
    id. Each Signal group has one channel per app: `bt/files` and `git-sha256/repos`.
  - App records go through the unchanged `COMMIT`, `ACCEPT` and `SERVE`.
  - Piece stores hold the bulk data. Six base ops (`0x17`-`0x1C`) bind, check, complete and
    assemble them.
  - Protocol 5 changes no protocol-4 layout, no store blob and no accept path.
- **Torrent.** One file of at most 64 MiB, in 1 MiB pieces. Members fetch it from the CDN and
  repair it by per-digest `SERVE` from any member seated in the announcement. There are two ops
  (`0x20`-`0x21`).
- **Git.**
  - Raw objects are the piece content: no zlib, no pack, and no idx in Lean.
  - `zrdtd` recomputes every object id. It checks each push against the pusher's whole channel
    table: the root rule, freshness, the gate and exact shares.
  - It computes the push log and the branch values from the channel store.
  - There are three ops (`0x28`-`0x2A`).
- **Lanes.** There are five parallel lanes: Lean base, torrent and git; fork transport and
  torrent-ui. A sixth, the git helper, is already running. Stage 1 takes about 4 days.
  Stage 2 takes about 7.5, starting at once against §B (§F).

## A. The demo beats (mock server)

### A.1 Torrent: group "Camping" (Alice, Bob, Carol, Dave)

Dave's desktop runs the demo-only hook `ZRDT_DEMO_VILLAIN=tamper`, so he plays a modified member.
The evil mock server (`demo/evil.ts`) plays the server.

1. **Alice shares.** She runs `zbt share ~/trip.mp4 --group Camping`. The fork's dialog asks
   "Share trip.mp4 (20 MiB) with Camping (4 members)?". The fork then:
   1. uploads the 20 slices of 1 MiB with fresh keys;
   2. runs the freeze job: `AUDIENCE`, `BT_BUILD`, `COMMIT`, a re-check of members and keys,
      then `ACCEPT` of announcement A into the channel;
   3. sends A as Content 205;
   4. binds her own A like any receiver: `PIECES_BIND`, 20 × `PIECE_ACCEPT` from the local
      file, `PIECES_COMPLETE` → `OK`.
2. **Bob and Dave fetch.** A came live from Alice, so `CLASSIFY` reports it confirmed by its
   author, and it is at most 32 MiB. Their forks therefore fetch it without a click. They run
   `PIECES_BIND`, then download and `PIECE_ACCEPT` each piece, then `PIECES_COMPLETE` → `OK`
   (heads {F}). Each writes the file into a new folder, and `ASSEMBLE` of the written file gives
   `OK`.
3. **Alice quits.** The server deletes the CDN objects of pieces 3, 7 and 12. It will also
   corrupt piece 15's ciphertext on the way to Carol.
4. **Carol starts her app.** A arrives from the queue.
   - 16 pieces pass `PIECE_ACCEPT`.
   - Pieces 3, 7 and 12 give 404s, and piece 15 fails Signal's attachment MAC.
   - `PIECES_COMPLETE` answers `MISSING` with exactly those four digests.
5. **Carol repairs.** She asks the members A seats for disjoint pieces, author first, at most 3
   requests at once: Alice {3}, Bob {12, 15}, Dave {7}.
   - Alice's request times out (`ZRDT_REPAIR_TIMEOUT_MS`, 5 s in the harness), and piece 3 goes
     to Bob.
   - Bob's sealed reply passes, and `PIECE_ACCEPT` gives `OK` twice.
   - Dave's reply has a flipped byte, so `PIECE_ACCEPT` gives `BAD_PIECE`. Only Carol sees "piece
     7 from Dave failed its check". She stops asking Dave, and piece 7 goes to Bob.

   Then `PIECES_COMPLETE` → `OK`, and `ASSEMBLE` → `OK`.

What this shows, and the theorem behind each claim (§C):
- The missing list is exact (`run_complete_missing`).
- Every byte is checked, from the CDN or from a member (`run_piece_accept`).
- Repair content goes only to A's audience (`serve_pieces`, `pieces_follow_announcement`).
- Everyone who completes holds the same bytes (`assemble_unique`).

On screen, as stated: **Signal's MAC catches the server; zrdt's check catches members.** The
piece-store code (heads {F}) shows completeness. It is F's digest, which A already fixes, so it
adds no agreement claim beyond `assemble_unique`.

### A.2 Git: group "Code" (Alice, Bob, Carol; Dave is added at step 5)

The repositories use `git init --object-format=sha256`. The remote URL `zrdt::Code/demo` names
Signal group "Code" and repository "demo". All repositories of a group share the group's one git
channel `git-sha256/repos`.

1. **Alice pushes.** She has commits c0 and c1 on `main`. She runs
   `git remote add team zrdt::Code/demo` and `git push team main`, which publishes push P1 (main:
   none → c1). Her table is complete (the channel is empty), so the root commit c0 may go.
2. **Bob clones.** He runs `git clone zrdt::Code/demo`. His fork has already fetched P1 and run
   `GIT_OBJECTS`, so `main` = c1.
3. **Bob force-pushes.** He amends c1 into c2 (parent c0) and runs `git push --force team main`.
   This publishes P2: main c1 → c2, forced. The gate passes, because Alice and Carol hold c0 and
   c1 through P1, and P1 assigned main := c1.
4. **The logs agree.** On all three screens, `git zrdt log` shows "Bob force-pushed main
   c1 → c2". `git zrdt status` shows the same compare code, and `team/main` = c2 (`refs_agree`,
   `force_visible`).
5. **Dave joins.** Dave is added to "Code" and runs `git clone zrdt::Code/demo`. His fork opens
   the channel relative and catches up (JOIN §6). He gets P1 and P2 as structure or boundary
   digests only. His clone is empty: "this repository has history you were not given". His
   compare code equals the others' (heads {P2}, `agree_rel`), but his view is not theirs:
   `refs_agree` needs every opening, and he has none (§C.3).
6. **Carol is blocked.** She commits c3 and runs `git push`. The fork's pre-check (`GIT_PREPARE`
   before any upload) refuses: `PUSH_REFUSED` `GATE`, Dave marked new. Nothing is sent, and git
   prints "Dave (new member) has not been given main; run `git zrdt share main`".
7. **Alice shares.** She runs `git zrdt share main`.
   1. The fork calls `GIT_PREPARE` with share set and an empty `expect`. The reply,
      `COVERS_CHANGED` [Dave], is the dialog's list.
   2. The dialog says "Share main@c2 with Dave: the files of c2, its message and author, and its
      parent's id; not its history".
   3. On confirm, the fork calls `GIT_PREPARE` again with `expect` = [Dave]. It returns `OK`, and
      share record S (main c2 → c2) is published.
8. **Dave gets c2, then c3.**
   - Dave fetches: `main` = c2 as a shallow clone, and his log shows only S.
   - Carol pushes again, and P3 passes: Dave holds c2 and all its objects through S, and S
     assigned main := c2.
   - Dave fetches c3.

Pinned by vectors, not shown on screen:
- A newcomer's root-commit push gets `ROOT`.
- A re-push of history that the table holds gets `OLD_OBJECT`.

What this shows:
- Every object is checked (`checkObjects_sound`, `run_git_objects`).
- A force push is in every complete-table member's log, and the codes match (`force_visible`).
- A newcomer gets nothing older until a deliberate share whose coverage is stated exactly
  (`checkPush_history`, `checkShare_exact`).

`zrdtd` does not check ancestry: "forced" is the pusher's flag. The helper's "not a
fast-forward" note comes from git.

## B. Protocol 5

`VERSION` replies 5 once lane base switches `Proto.protocolVersion` (§E.1); until then it replies
4, and every op from `0x17` replies `UNKNOWN_OP`. Protocol-4 layouts are unchanged.
`zrdtd` answers with `Zrdt.Apps.handle`, which sends:
- op bytes `0x17`-`0x1F` to `Zrdt.AppBase` (base);
- `0x20`-`0x27` to `Zrdt.Torrent`;
- `0x28`-`0x2F` to `Zrdt.Git`;
- every other byte to `Proto.run` (protocol 4).

`0x00` and `0x30`-`0xFF` stay unknown.

### B.1 New field types

All numbers are big-endian, as in protocol 4.

| Type | Bytes |
|---|---|
| `u16`, `u64` | 2 and 8 bytes |
| `ordered` | `u32` count, then that many `digest`s **in index order** (not sorted; protocol 4's "every digest list in a reply is sorted" does not apply) |
| `oid` | 32 bytes, a SHA-256 git object id |
| `optoid` | `u8` 0, or `u8` 1 ‖ `oid` |
| `seat` | `aci` ‖ `tag` (16) |
| `seats` | `u32` count, then that many `seat`s, strictly increasing by (aci, tag) |
| `refname` | `u8` length (1-250), then the bytes |
| `update` | `refname` ‖ old (`optoid`) ‖ new (`optoid`) ‖ forced (`flag`) |
| `updates` | `u8` count (at most 16), then that many `update`s |
| `helds` | `u32` count, then that many protocol-4 `held` (`digest` ‖ `opening`) |

### B.2 Encodings (reference code: `core/Zrdt/AppBase.lean`)

**Protobuf field keys.**
- 201 `CA 0C`, 210 `92 0D`, 211 `9A 0D`, 212 `A2 0D`, 215 `BA 0D`, 216 `C2 0D`: length-delimited.
- 220 `E0 0D`: a varint.
- 221 `EA 0D`, 225 `8A 0E`, 226 `92 0E`: length-delimited.

Varints are minimal.

**App message** (`appMessage`). These are the committed bytes of a channel record, which is
Content 205 without fields 15 and 200:

    [201 audience] [210 app] [211 channel] [212 body] [215 descriptor]? [216 pointers]?

- The fields come in this order. Each is length-delimited. 201-212 appear once each, and 215
  and 216 at most once.
- The parser (`appHeader`) accepts only bytes that `appMessage` writes back identically, so the
  meaning of an app record is unique.
- `wellFormed`:
  - the audience passes `Serve.parseAudience`;
  - app and channel are 1-64 bytes;
  - body ≤ 24 KiB;
  - pointers ≤ 16 KiB.
- There is no field 1, 5 or 14. So an app record is never shown as chat and is never ephemeral.

**Ids.**
- `channelId(sg, app, name)` = SHA-256(`"zrdtC1"` ‖ Signal group id (32) ‖ u8 |app| ‖ app ‖
  u8 |name| ‖ name).
- `storeId(channel, author, store nonce)` = SHA-256(`"zrdtT1"` ‖ channel ‖ author (16) ‖
  nonce (32)).
- `pieceNonce(store nonce, i)` = SHA-256(`"zrdtN1"` ‖ store nonce ‖ u32 i). The manifest uses
  i = 2^32 - 1.
- `commitOf(g, a, n, m)` = SHA-256(`"zrdtP1"` ‖ g ‖ a ‖ n ‖ m). This is `Zrdt.commit` of a
  message without field 15 or 200.

**Descriptor** (field 215):

    "zrdtD1" ‖ store nonce (32) ‖ u64 L ‖ u8 k ‖ ordered (u32 N ‖ N digests) ‖ manifest (bytes)

It is well-formed when all of these hold:
- k ∈ {20, 10}: hosts always use 20, and 10 exists only so that vectors stay small;
- 1 ≤ L ≤ 64 · 2^k;
- N = ⌈L / 2^k⌉, with no repeated digest;
- manifest ≤ 4 KiB.

F is not carried: `zrdtd` derives it.

**Piece i** of stream s is bytes [i·2^k, (i+1)·2^k) of s (the last piece is short).
- Committed bytes: `[201 A's audience] [220 i] [221 bytes]`.
- Opening: `pieceNonce(nonce, i)` ‖ the committed bytes. Only `zrdtd` builds it, so a responder
  rebuilds it from the bytes.
- Record: (storeId, `commitOf`(storeId, author, pieceNonce, committed bytes), no links, A's
  author).

**Manifest F.**
- Committed bytes: `[201 A's audience] [225 the N digests in index order] [226 app manifest]`.
- Record: (storeId, its commitment, links = the N digests, A's author).
- A complete piece store has heads {F}.

**`pieceOk(ctx, i, b)`** holds when i < N, |b| = the length of piece i, and the piece record's
digest is `ordered[i]`. **`assembleOk(ctx, s)`** holds when |s| = L and every slice passes
`pieceOk`.

**Piece context** (`PieceCtx`, from `bindCtx`). It holds A's digest, A's group (the channel),
A's author, A's app header, A's parsed audience and A's descriptor.
- It lives in memory only and is not persisted.
- After a restart, the host binds again and re-runs `PIECE_ACCEPT` over the bytes it kept, one
  hashing pass at about 50 MiB/s.

### B.3 Limits

| Item | Limit |
|---|---|
| Stream | 1 B ≤ L ≤ 64 MiB at k = 20; N ≤ 64. A git push with no objects has L = 0: no 215, no 216, no piece store |
| Fields | body (212) ≤ 24 KiB; app manifest (226) ≤ 4 KiB; pointers (216) ≤ 16 KiB; app tag and channel name 1-64 bytes |
| Content 205 | ≤ 64 KiB, checked by the host before sending. Audience ≤ 256 entries, as in JOIN |
| Repair | ≤ 8 pieces per request; a responder runs one sealed upload at a time; a sealed reply over 48 KiB goes as `sealedOnCdn` (every 1 MiB piece does) |
| Torrent | one file; its name passes `safeComponent` |
| Git | ≤ 512 objects and ≤ 16 ref updates per push; `refs/heads/*` and `refs/tags/*` only; commit, tree and blob objects only; repository names 1-64 bytes of `[A-Za-z0-9._-]`, first byte alphanumeric |

### B.4 Statuses (all fixed in the skeleton's `Proto.Code`)

| Byte | Name | Lane | Body |
|---|---|---|---|
| `0x0C` | `BAD_PIECE` | base | `PIECE_ACCEPT`, `PIECE_OPENING`: empty. `ASSEMBLE`, `GIT_OBJECTS`: `u32` first bad index (N if the length is not L) |
| `0x0D` | `BAD_APP` | base | reason `u8`: 1 `NOT_STORED` (A not in the channel, or the channel is not `channelId(sg, app, name)`), 2 `OPENING`, 3 `NOT_APP`, 4 `NOT_SEATED`, 5 `DESCRIPTOR`, 6 `LIMITS`, 7 `WRONG_APP` (the piece key's context belongs to another app) |
| `0x0E` | `BAD_NAME` | torrent | empty |
| `0x10` | `PUSH_REFUSED` | git | reason `u8` (1 `ROOT`, 2 `OLD_OBJECT`, 3 `GATE`, 4 `BAD_SHARE`, 5 `KEY_CHANGED`, 6 `COVERS_CHANGED`) ‖ `u32` count ‖ (`seat` ‖ `u8` mark: 0 new, 1 key changed, 2 covered) ‖ `u32` count ‖ `refname` ‖ `u32` count ‖ `oid` |
| `0x11` | `BAD_OBJECTS` | git | reason `u8` (1 `MALFORMED`, 2 `KIND`, 3 `GITLINK`, 4 `HEADER`, 5 `ORDER`, 6 `LIMITS`, 7 `NAME`, 8 `LIST`) ‖ `oid` (zero when there is none) |
| `0x12` | `OPENINGS_MISSING` | git | `digests`: stored channel records with a recorded audience but no held opening |

`0x0F` and `0x13`-`0x7F` are unassigned. A lane that needs a new status asks lane base.

### B.5 Base ops (lane base, `Zrdt.AppBase`)

| Op | Name | Request | Reply |
|---|---|---|---|
| `0x17` | `CHANNEL` | signal group (`group`) ‖ app (`str`) ‖ name (`str`) | `OK`: channel id (`group`); `BAD_APP` 6 |
| `0x18` | `PIECES_BIND` | piece key (`str`) ‖ channel key (`str`) ‖ signal group (`group`) ‖ app (`str`) ‖ own `aci` ‖ own `key` ‖ A (`bytes`, its encoding) ‖ A's `opening` | `OK`: `u64` L ‖ `u8` k ‖ `ordered` ‖ body (`bytes`) ‖ manifest (`bytes`) ‖ pointers (`bytes`, empty if absent); `MALFORMED`; `BAD_APP`; `NO_CHAT`; `CHAT_OPEN` |
| `0x19` | `PIECE_ACCEPT` | piece key ‖ `u32` i ‖ piece (`bytes`) | `OK`: `digest`; `BAD_PIECE`; `NO_CHAT` |
| `0x1A` | `PIECE_OPENING` | piece key ‖ `u32` i ‖ piece (`bytes`) | `OK`: the `opening`; `BAD_PIECE`; `NO_CHAT` |
| `0x1B` | `PIECES_COMPLETE` | piece key | `ACCEPT`'s reply for F with its opening: `OK` (`digest` ‖ encoding) or `MISSING` (`digests`); `NO_CHAT` |
| `0x1C` | `ASSEMBLE` | piece key ‖ stream (`bytes`) | `OK`; `BAD_PIECE`; `NO_CHAT` |

`0x1D`-`0x1F` are reserved.

**`PIECES_BIND`.** It checks, in order:
1. `NO_CHAT`: the channel key is not open.
2. `CHAT_OPEN`: the piece key is in use, as a chat or as a piece store.
3. `MALFORMED`: A's bytes are not a record.
4. `BAD_APP` 1: A is not stored in the channel.
5. `bindCtx`, which gives `BAD_APP` 2, 3 or 5:
   - the opening matches A;
   - it commits a canonical app message whose app is the requested app;
   - `channelId(sg, app, committed channel name)` = A's group;
   - it carries a well-formed descriptor.
6. `BAD_APP` 4: A's audience must seat (own `aci`, own `key`) with a non-zero tag. This is
   T-m12, now in Lean.

On `OK`, it opens an empty **closed** store with group `storeId` under the piece key and records
the context. The host uses hex(A's digest) as the piece key (T-m10).

**`PIECE_ACCEPT`.** If `pieceOk`, it accepts the piece record into the piece store and records
the context's audience for it; otherwise `BAD_PIECE`, and nothing changes. It is the only way a
piece enters a store.

**`PIECE_OPENING`.** Read-only. It is the responder's opening for `SERVE`'s `held` list.

**`PIECES_COMPLETE`.** Protocol 4's `accept` of F with its opening. `MISSING` lists exactly the
piece digests not stored, and changes nothing. `OK` leaves the store with heads {F}.

**`ASSEMBLE`.** Read-only: `assembleOk`, or the first bad index.

### B.6 Torrent ops (lane torrent, `Zrdt.Torrent`)

**Body (212):** exactly `"zbt1"`. **App manifest (226):** `"zbtF1"` ‖ name (`str`) ‖ `u64` L.

**`safeComponent(name)`**, all of these:
- 1-255 bytes of UTF-8;
- not `.` or `..`;
- no `/`, `\`, `:`, `<`, `>`, `"`, `|`, `?`, `*`, NUL, byte below `0x20`, or DEL;
- no leading or trailing space or dot;
- not a Windows reserved name (CON, PRN, AUX, NUL, COM1-9, LPT1-9; any case; with or without an
  extension).

| Op | Name | Request | Reply |
|---|---|---|---|
| `0x20` | `BT_BUILD` | channel (`group`) ‖ author (`aci`) ‖ store `nonce` ‖ `u8` k ‖ audience (`bytes`, `AUDIENCE`'s value) ‖ name (`str`) ‖ pointers (`bytes`) ‖ stream (`bytes`) | `OK`: message (`bytes`: A's committed bytes) ‖ `ordered`; `BAD_NAME`; `BAD_APP` 6 |
| `0x21` | `BT_FILE` | piece key | `OK`: name (`str`) ‖ `u64` L; `BAD_APP` 5 (the manifest is malformed, or its L is not the descriptor's), 7; `BAD_NAME`; `NO_CHAT` |

`0x22`-`0x27` are reserved. Both ops only read the state.

`BT_BUILD` returns `appMessage` with:
- app `"bt"`, channel `"files"`, body `"zbt1"`;
- the descriptor (nonce, L, k, the digests of the slices under a context with this channel,
  author and audience, and the manifest);
- pointers, if non-empty.

So the host never assembles an app message itself.

### B.7 Git ops (lane git, `Zrdt.Git`)

**Objects.** Each object is raw: `<type> SP <decimal length> NUL <content>`, where the type is
`commit`, `tree` or `blob`, and the length has no leading zero. Its id is SHA-256(raw), which is
a SHA-256 repository's object id. The **stream** is the push's raw objects, concatenated, with
ids strictly increasing. The host sorts them; Lean refuses unsorted input.

**`checkObjects`** recomputes every id and refuses with `BAD_OBJECTS`:
- `KIND`: a tag object.
- `GITLINK`: mode 160000 in a tree.
- `MALFORMED`: a malformed tree. Entries must be `<mode> SP <name> NUL <32 bytes>`, with mode
  in {100644, 100755, 120000, 40000}, name non-empty without `/` or NUL and not `.` or `..`, in
  git's tree order with no repeat.
- `HEADER`: a commit whose header is not exactly `tree <64 hex>`, then any number of
  `parent <64 hex>`, then `author`, `committer`, and an optional `encoding`, then a blank line.
  This allow-list refuses `gpgsig`, `gpgsig-sha256`, `mergetag`, continuation lines and unknown
  headers (R2, G-m9).

References: a commit references its tree and parents, and a tree references its entries.

**Push body (212):**

    "zgit1" ‖ flags u8 (bit 0 share; other bits 0) ‖ repo (u8 len ‖ name) ‖ updates
      ‖ u16 nO ‖ nO oids (strictly increasing) ‖ u16 nC ‖ nC seats (covers)

- An update's old is the value the pusher saw and replaces (G-M2).
- A missing old means a create, and a missing new means a delete.
- Ref names pass `validRefName` (GIT_PLAN §2.3) and are distinct within a push.
- Covers are empty unless the push is a share.
- A push that carries objects has 215 and 216, like any announcement.

**The table** (`tableOf`). Its entries are the stored records of the channel store that have a
held opening that matches them and that is a canonical app message of `git-sha256` / `repos`
with a parseable push body. Each entry holds (digest, author, seats, body).
- **complete**: the channel store has no boundary digest, and every stored record has a
  recorded audience. So, by `OPENINGS_MISSING`, it has a held opening.
- **entitled(s, o)**: some entry lists o among its carried ids, and its audience seats s (same
  ACI and tag, and the tag is not zero).
- **keyChanged(s)**: some entry seats s's ACI under another non-zero tag.
- **assigns(e, repo, n, v)**: entry e has an update of (repo, n) whose new value is v.
- **refsOut**: the ids the carried objects reference, plus every update's old and new value,
  minus the carried ids.
- **checked seats**: the push audience's seats with a non-zero tag, other than the author's own
  ACI.

| Op | Name | Request | Reply |
|---|---|---|---|
| `0x28` | `GIT_PREPARE` | signal group (`group`) ‖ channel key (`str`) ‖ author (`aci`) ‖ store `nonce` ‖ `u8` k ‖ audience (`bytes`) ‖ share (`flag`) ‖ expect (`seats`) ‖ repo (`str`) ‖ `updates` ‖ `helds` ‖ pointers (`bytes`) ‖ stream (`bytes`) | `OK`: message (`bytes`) ‖ `ordered` (empty when L = 0) ‖ covers (`seats`); `PUSH_REFUSED`; `BAD_OBJECTS`; `OPENINGS_MISSING`; `BAD_OPENING`; `BAD_APP` 1, 6; `NO_CHAT` |
| `0x29` | `GIT_OBJECTS` | piece key ‖ stream (`bytes`) | `OK`: `u32` count ‖ per object, in stream order: kind `u8` (1 commit, 2 tree, 3 blob) ‖ `oid` ‖ `u64` offset ‖ `u64` length; `BAD_PIECE`; `BAD_OBJECTS`; `BAD_APP` 7; `NO_CHAT` |
| `0x2A` | `GIT_VIEW` | signal group ‖ channel key ‖ repo (`str`) ‖ `helds` | `OK`: log (`u32` count ‖ `digest` ‖ author `aci` ‖ share `flag` ‖ `update`, sorted by digest, then ref name) ‖ refs (`u32` count ‖ `refname` ‖ `digest` ‖ value `optoid`, the live assignments, sorted); `BAD_OPENING`; `OPENINGS_MISSING`; `BAD_APP` 1; `NO_CHAT` |

`0x2B`-`0x2F` are reserved. All three ops only read the state.

**`GIT_PREPARE`'s checks, in order.**
1. `NO_CHAT`.
2. `BAD_APP` 1 (the channel store's group ≠ `channelId(sg, "git-sha256", "repos")`) and
   `BAD_APP` 6 (the audience).
3. `BAD_OPENING`: a held opening does not match its stored record.
4. `OPENINGS_MISSING`.
5. `BAD_OBJECTS`: `checkObjects`, the limits, the repository and ref names, and a delete in a
   share.
6. **Root rule (G-F1).** A non-share push that carries a commit with no parent needs a
   **complete** table; otherwise `ROOT`, with the root ids.
7. **Freshness (G-M6).** A non-share push carries no id that any entry lists; otherwise
   `OLD_OBJECT`, with the ids.
8. **Gate (G-M1).** For a non-share push, every checked seat must be:
   - entitled to every id of refsOut;
   - for every update with old = v, seated in an entry that assigns (repo, name, v) (the name
     rule).

   Otherwise `GATE`, with each failing seat marked new (seated in no entry) or key changed.
   Only new seats get the share hint.
9. **Shares (G-M7).** A share push must meet all of these:
   - `BAD_SHARE` unless the carried commits are exactly the updates' new values, refsOut ⊆
     those commits' parents, there is no delete, and every old is absent or equal to its new
     value;
   - covers = the checked seats that are not entitled to some carried id that an entry lists;
   - `KEY_CHANGED` if a covered seat has keyChanged;
   - `COVERS_CHANGED`, with the covers marked 2, unless covers = `expect`.

   The fork gets the dialog's list from a first call with an empty `expect`.

The reply is `appMessage` with app `"git-sha256"`, channel `"repos"`, the push body, the
descriptor and the pointers (both only when L > 0).

**Why the whole table (G-F1).** Freshness, the gate and the name rule read the pusher's whole
table, not the causal past. Links play no part, so a push that drops them gains nothing. One
channel per Signal group means that a second repository name does not start from an empty table.
A root commit, which could be the start of a re-sent history, goes only from a complete table,
where freshness sees every earlier object. Two kinds of member have incomplete tables: a
newcomer, and a member whose key changed or who lost his device (a relative store). Neither can
re-send a history from its root. The residual is in §H.

**`GIT_VIEW`.**
- **Log:** every update of every entry whose repo is `repo`, as (digest, author, share, update).
- **Register:** an assignment (d, n, v) is superseded when another entry e has an update of n
  with old = v, and d is reachable from e's links in the channel store. The live assignments are
  those not superseded.
- **The helper's listing:** a single live non-empty value is `refs/heads/n`. Several distinct
  values are listed as `n.zrdt-<12 hex of d>`, with no plain name (G-M3), and only deletes means
  absent. HEAD is `refs/heads/main` if it exists.

### B.8 Protocol-4 ops on piece keys, and reuse

`Zrdt.Apps.runV4` (in the skeleton) handles protocol-4 ops on a piece key:
- the read-only ops (`HEADS`, `HAS`, `GET`, `REACH_SET`, `CLASSIFY`, `ENCODE`, `SERVE`,
  `ADDRESSED`, `LINKABLE`) run unchanged on the piece stores;
- `CLOSE` drops the store and its context;
- `NEW`, `NEW_RELATIVE`, `OPEN` and `SALVAGE` reply `CHAT_OPEN`;
- `ACCEPT`, `ACCEPT_RECORD`, `ACCEPT_VIEW` and `MERGE` reply `BAD_REQUEST`.

So a piece store holds only F and pieces whose bytes this `zrdtd` checked (TORRENT_PLAN C5).

On channel stores, every protocol-4 op is unchanged. The work is done by `COMMIT`, `ACCEPT`,
catch-up `SERVE` and `ACCEPT_VIEW` (channel repair and newcomers), `AUDIENCE`, `CLASSIFY` (the
fetch policy) and `HEADS` (compare codes). Piece repair is the unchanged per-digest `SERVE` on
the piece key, with `PIECE_OPENING`'s openings as `held`.

### B.9 The fork: wire and flows

**Wire.**
- Content field 205 is `ZrdtAppMessage`: field 15 (groupV2) ‖ field 200 (`ZrdtMeta`: links and
  nonce) ‖ the committed bytes exactly as `BT_BUILD` or `GIT_PREPARE` returned them.
- The receiver passes the field-205 bytes **as received** to `COMMIT`, not a re-encoding, and
  gets the opening `ACCEPT` needs.
- Field 216 holds `ZrdtPointers { repeated AttachmentPointer pieces = 1; }`.
- `ZrdtServeRequest` gains `7 bytes announcement` (A's digest, for piece repair) and
  `8 bytes channel` (a channel id, for channel catch-up).
- `ZrdtServed` gains `5 AttachmentPointer sealedOnCdn`.

**Author** (one queue job per announcement):
1. Git only: `GIT_PREPARE` as a pre-check, with empty pointers. A refusal stops here, before any
   upload.
2. Slice the stream and upload the N slices with fresh keys, bypassing Desktop's reuse cache.
3. The freeze job:
   1. `AUDIENCE`.
   2. `BT_BUILD` or `GIT_PREPARE`, with the pointers.
   3. `COMMIT`.
   4. Re-read members and identity keys. If any changed, restart the job (T-M1, G-M1). The
      uploads are reused, and a job is never resumed after a restart.
   5. `ACCEPT` into the channel.
   6. Send Content 205 to recipients ⊆ seats, with a send type the sendLog does not keep (T-M2,
      G-m4).
4. Bind its own A as a receiver does (`PIECES_BIND`, `PIECE_ACCEPT` from local bytes,
   `PIECES_COMPLETE`). The author is then a responder.

**Receiver.**
1. `COMMIT` of the received bytes, then `ACCEPT` A. A gap goes to the usual repair.
2. **Fetch policy.** The torrent fetches automatically only an A that `CLASSIFY` reports as
   confirmed by its author, up to 32 MiB; any other A needs a click (T-M4). Git fetches every
   push.
3. `PIECES_BIND`. On `BAD_APP` 4, never offer, open or fetch (T-m12).
4. Download each piece and run `PIECE_ACCEPT`. A 404 or a MAC failure goes to repair. A
   `BAD_PIECE` on CDN bytes that passed the MAC means the author uploaded wrong bytes: blame A's
   author.
5. `PIECES_COMPLETE`. On `MISSING`, repair. On `OK`, the app's step:
   - torrent: write with `mkdirat` and `O_CREAT|O_EXCL|O_NOFOLLOW` into a new folder, then
     `ASSEMBLE` of the written file;
   - git: `GIT_OBJECTS`, then the helper stores each object with
     `git hash-object -w -t <kind> --stdin` and compares the id.

**Repair.**
- **Requester.** It sends a per-digest `ZrdtServeRequest{groupId, rid, wanted (≤ 8),
  announcement}` 1:1, only to current members that A seats.
  - It asks the author first, with at most 3 requests in flight, on disjoint pieces.
  - It reassigns a piece on timeout or `BAD_PIECE`, and stops asking a member after a bad piece.
    Only this user is told.
- **Responder.**
  - It checks that the requester is a current member of the channel's Signal group (T-m11), and
    finds the piece store by A's digest (T-m10).
  - It runs `PIECE_OPENING` for each wanted piece it holds, then per-digest `SERVE` on the piece
    key, then the JOIN seal.
  - A reply over 48 KiB goes as `sealedOnCdn`. The responder runs one sealed upload at a time.
- **Requester, on a reply.** It runs the JOIN §4.4 checks, takes (i, bytes) from fields 220 and
  221 of each addressed entry's opening, and runs `PIECE_ACCEPT`. A host bug in this extraction
  gives `BAD_PIECE`, never acceptance.

### B.10 The local endpoint (the git helper's, and `zbt`'s)

The git helper lane is writing `tools/git-remote-zrdt/ENDPOINT.md` in the zrdt repo. **It is
authoritative for routes and JSON.** The fork implements it, and the two are aligned at
integration. This plan fixes only the properties below. If ENDPOINT.md contradicts one, the
transport lane raises it with kejace.
- It is HTTP on 127.0.0.1 only. Each desktop picks a port and writes it with a random token to
  `<userData>/zrdt-apps.json` (mode 0600). Tools find the file through `ZRDT_ENDPOINT` or
  `git config zrdt.endpoint`, since each demo desktop has its own `userData`.
- Every request carries the token. A client is scoped to one app and sees only that app's
  channels.
- No route exposes pointers, openings, nonces, piece keys or `SERVE`.
- A share happens only after the fork's own dialog.
- Git objects cross the endpoint raw (the stream, or one object per entry), never as a pack.

## C. Theorems per lane

The statements below are the targets. A lane may strengthen a statement, but must not weaken it,
and must keep its name. Names in `Zrdt.AppBase` exist in the skeleton. The constructor names of
requests and replies (`.pieceAccept`, `.digest`, ...) are fixed here for the lanes to use.
`Sha256Collision` is `∃ x y : ByteArray, x ≠ y ∧ sha256 x = sha256 y`. Advertised statements spell
it out, as `audience_bound` does.

A record-digest collision reduces to `Sha256Collision` in core, through `decode_encode`. Every
theorem needs only the standard axioms, and needs no `sorry`, `native_decide` or new axiom.
`[M]` marks a statement that needs Mathlib or `Api.lean`; everything else stays in `core/`.

### C.1 Lane base: encodings, tag separation, the dispatcher (`core/Zrdt/AppBase.lean`, `Apps.lean`)

```lean
namespace Zrdt.AppBase
-- App messages: canonical round trip, so the encoding is injective and its meaning unique.
theorem appHeader_appMessage {h : AppHeader} (hw : h.wellFormed = true) :
    appHeader (appMessage h) = some h
theorem appMessage_appHeader {m : ByteArray} {h : AppHeader} (hm : appHeader m = some h) :
    appMessage h = m ∧ h.wellFormed = true
theorem committedBytes_appMessage {h : AppHeader} (hw : h.wellFormed = true) :
    committedBytes (appMessage h) = some (appMessage h)        -- COMMIT keeps it whole
theorem appOf_audience {o : ByteArray} {h : AppHeader} (ho : appOf o = some h) :
    Serve.audienceOf o = Serve.parseAudience h.audience ∧ (Serve.audienceOf o).isSome
-- Tag separation from chat records.
theorem app_not_chat {o : ByteArray} {h : AppHeader} (ho : appOf o = some h) :
    Serve.ephemeral o = false ∧ ∀ n m fs, splitOpening o = some (n, m) → fields m = some fs →
      ∀ f ∈ fs, f.num ∈ [201, 210, 211, 212, 215, 216]
theorem appOf_pieceOpening (c : PieceCtx) (i : Nat) (b : ByteArray) :
    appOf (pieceOpening c i b) = none
theorem appOf_manifestOpening (c : PieceCtx) : appOf (manifestOpening c) = none
theorem opening_bound {g : GroupId} {a : Aci} {c : Digest} {o₁ o₂ : ByteArray}
    (h₁ : openingMatches g a c o₁ = true) (h₂ : openingMatches g a c o₂ = true) :
    o₁ = o₂ ∨ Sha256Collision
theorem app_bound {g : GroupId} {a : Aci} {c : Digest} {o₁ o₂ : ByteArray}
    (h₁ : openingMatches g a c o₁ = true) (h₂ : openingMatches g a c o₂ = true) :
    appOf o₁ = appOf o₂ ∨ Sha256Collision                     -- one record, one app meaning
theorem channelId_inj {g g' : GroupId} {p p' n n' : ByteArray}
    (hs : p.size < 256 ∧ p'.size < 256 ∧ n.size < 256 ∧ n'.size < 256)
    (h : channelId g p n = channelId g' p' n') : (g = g' ∧ p = p' ∧ n = n') ∨ Sha256Collision
theorem storeId_ne_channelId {c g : GroupId} {a : Aci} {k : Nonce} {p n : ByteArray}
    (h : storeId c a k = channelId g p n) : Sha256Collision
-- Descriptor and piece encodings.
theorem Descriptor.parse_write (d : Descriptor) (hw : d.wellFormed = true) :
    Descriptor.parse d.write = some d
theorem Descriptor.write_parse {b : ByteArray} {d : Descriptor} (h : Descriptor.parse b = some d) :
    d.write = b
theorem pieceOpening_matches (c : PieceCtx) (i : Nat) (b : ByteArray) (hi : i < 2 ^ 32)
    (ha : Serve.parseAudience c.header.audience = some c.seats) :
    openingMatches c.storeId c.author (pieceRecord c i b).commit (pieceOpening c i b) = true ∧
      Serve.audienceOf (pieceOpening c i b) = some c.seats
theorem manifestOpening_matches (c : PieceCtx)
    (ha : Serve.parseAudience c.header.audience = some c.seats) :
    openingMatches c.storeId c.author (manifestRecord c).commit (manifestOpening c) = true ∧
      Serve.audienceOf (manifestOpening c) = some c.seats
end Zrdt.AppBase

namespace Zrdt.Apps
-- The dispatcher keeps protocol 4: off piece keys it is `Proto.run` on the chats, so every
-- protocol-4 theorem (run_serve_content, accept_accepted, ...) holds under protocol 5.
theorem runV4_chats {build : String} {s : AppBase.State} {q : Proto.Request}
    (h : ∀ c b, chatKey? q = some (c, b) → s.pieces.contains c = false) :
    runV4 build s q = ((Proto.run build s.chats q).1, { s with chats := (Proto.run build s.chats q).2 })
theorem runV4_pieces_mutating {build : String} {s : AppBase.State} {q : Proto.Request} {c : String}
    (hk : chatKey? q = some (c, false)) (hp : s.pieces.contains c = true)
    (hc : ∀ c', q ≠ .close c') : (runV4 build s q).2 = s
theorem run_channel {build : String} {s s' : AppBase.State} {sg g : GroupId} {p n : String}
    (h : run build s (.base (.channel sg p n)) = (.base (.channel g), s')) :
    g = AppBase.channelId sg p.toUTF8 n.toUTF8 ∧ s' = s
end Zrdt.Apps
```

### C.2 Lane torrent: piece stores and the torrent (`core/Zrdt/PieceProofs.lean`, `Torrent.lean`)

The torrent lane proves the piece-store theorems. They guard the bulk data of both apps.
`pieceOk_unique`, `bindCtx_unique` and `assemble_unique` use only the skeleton's definitions, so
they start now. The `run_*` and `PiecesInv` statements start when lane base's ops land (§F).

```lean
namespace Zrdt.PieceProofs
open AppBase
theorem pieceOk_unique {c : PieceCtx} {i : Nat} {b₁ b₂ : ByteArray}
    (h₁ : pieceOk c i b₁ = true) (h₂ : pieceOk c i b₂ = true) : b₁ = b₂ ∨ Sha256Collision
theorem bindCtx_unique {sg₁ sg₂ : GroupId} {p₁ p₂ o₁ o₂ : ByteArray} {A₁ A₂ : Rec}
    {c₁ c₂ : PieceCtx} (hA : hashRecord A₁ = hashRecord A₂)
    (h₁ : bindCtx sg₁ p₁ A₁ o₁ = .ok c₁) (h₂ : bindCtx sg₂ p₂ A₂ o₂ = .ok c₂) :
    c₁ = c₂ ∨ Sha256Collision
theorem assemble_unique {sg₁ sg₂ : GroupId} {p₁ p₂ o₁ o₂ s₁ s₂ : ByteArray} {A₁ A₂ : Rec}
    {c₁ c₂ : PieceCtx} (hA : hashRecord A₁ = hashRecord A₂)
    (h₁ : bindCtx sg₁ p₁ A₁ o₁ = .ok c₁) (h₂ : bindCtx sg₂ p₂ A₂ o₂ = .ok c₂)
    (hs₁ : assembleOk c₁ s₁ = true) (hs₂ : assembleOk c₂ s₂ = true) : s₁ = s₂ ∨ Sha256Collision
-- Every accepted byte was checked against the digest A committed for its index.
theorem run_piece_accept {build : String} {s s' : State} {key : String} {i : Nat}
    {b : ByteArray} {d : Digest}
    (h : Apps.run build s (.base (.pieceAccept key i b)) = (.base (.digest d), s')) :
    ∃ ctx ch, s.ctxs[key]? = some ctx ∧ pieceOk ctx i b = true ∧ ctx.desc.ordered[i]? = some d ∧
      d = hashRecord (pieceRecord ctx i b) ∧ s'.pieces[key]? = some ch ∧
      ch.store.get d = some (pieceRecord ctx i b) ∧ ch.audiences[d]? = some ctx.seats
theorem run_piece_refused {build : String} {s s' : State} {key : String} {i : Nat}
    {b : ByteArray} (h : Apps.run build s (.base (.pieceAccept key i b)) = (.base (.badPiece none), s')) :
    s' = s ∧ ∀ ctx, s.ctxs[key]? = some ctx → pieceOk ctx i b = false
-- The exact missing list.
theorem run_complete_missing {build : String} {s s' : State} {key : String} {F : Rec}
    {ds : Array Digest}
    (h : Apps.run build s (.base (.piecesComplete key)) = (.base (.accept F (.missing ds)), s')) :
    s' = s ∧ ∃ ctx ch, s.ctxs[key]? = some ctx ∧ s.pieces[key]? = some ch ∧
      F = manifestRecord ctx ∧ ∀ d, d ∈ ds ↔ (d ∈ ctx.desc.ordered ∧ ch.store.has d = false)
theorem run_complete_ok {build : String} {s s' : State} {key : String} {F : Rec} {d : Digest}
    (h : Apps.run build s (.base (.piecesComplete key)) = (.base (.accept F (.accepted d)), s')) :
    ∃ ctx ch, s.ctxs[key]? = some ctx ∧ F = manifestRecord ctx ∧ d = hashRecord F ∧
      s'.pieces[key]? = some ch ∧ ch.store.headsArray = #[d] ∧
      ∀ e ∈ ctx.desc.ordered, ch.store.has e = true
theorem run_bind {build : String} {s s' : State} {key ck : String} {sg : GroupId} {p : String}
    {me : Aci} {k aB o : ByteArray} {ctx : PieceCtx}
    (h : Apps.run build s (.base (.piecesBind key ck sg p me k aB o)) = (.base (.bound ctx), s')) :
    ∃ A ch, decode aB = some A ∧ s.chats[ck]? = some ch ∧ ch.store.has (hashRecord A) = true ∧
      bindCtx sg p.toUTF8 A o = .ok ctx ∧ Serve.seats ctx.seats me k = true ∧
      s.pieces.contains key = false ∧ s.chats.contains key = false ∧ s'.ctxs[key]? = some ctx
-- The invariant: a piece store holds F and checked pieces only, each with A's audience.
def PiecesInv (s : State) : Prop :=
  ∀ key ch, s.pieces[key]? = some ch → ∃ ctx, s.ctxs[key]? = some ctx ∧
    Serve.parseAudience ctx.header.audience = some ctx.seats ∧
    (∃ c, ch.store = .closed c) ∧ ch.store.group = ctx.storeId ∧
    ∀ d r, ch.store.get d = some r →
      (r = manifestRecord ctx ∨ ∃ i b, pieceOk ctx i b = true ∧ r = pieceRecord ctx i b) ∧
      ∀ a, ch.audiences[d]? = some a → a = ctx.seats
theorem piecesInv_empty : PiecesInv {}
theorem run_piecesInv {build : String} {s : State} (q : Apps.Request) (h : PiecesInv s) :
    PiecesInv (Apps.run build s q).2
theorem pieces_follow_announcement {s : State} {key : String} {ch : Proto.Chat}
    {ctx : PieceCtx} {d : Digest} {r : Rec} {o : ByteArray} (hI : PiecesInv s)
    (hp : s.pieces[key]? = some ch) (hc : s.ctxs[key]? = some ctx)
    (hr : ch.store.get d = some r) (ho : openingMatches r.group r.author r.commit o = true) :
    Serve.audienceOf o = some ctx.seats ∨ Sha256Collision
theorem serve_pieces {build : String} {s s' : State} {key : String} {sr : Proto.ServeRequest}
    {hd : Proto.ServeHeader} {es : List Serve.Entry} {ctx : PieceCtx} {r : Rec}
    {o : ByteArray} {ac : Bool} (hI : PiecesInv s) (hc : s.ctxs[key]? = some ctx)
    (h : Apps.run build s (.v4 (.serve key sr)) = (.v4 (.served hd es), s'))
    (he : Serve.Entry.addressed r (some o) ac ∈ es) :
    s' = s ∧ (Serve.seats ctx.seats sr.requester sr.key = true ∨ Sha256Collision)
end Zrdt.PieceProofs

namespace Zrdt.Torrent
open AppBase
-- The author's own announcement makes her file fetchable: any bind of it accepts her stream.
-- `nc`: the store nonce; `e`: log₂ of the piece size; `n`: A's commitment nonce (COMMIT's).
theorem btBuild_complete {ch sg : GroupId} {a : Aci} {nc n : Nonce} {e : Nat}
    {aud ptrs s msg : ByteArray} {name : String} {ord : Array Digest} {ls : Array Digest}
    {ctx : PieceCtx} (hb : btBuild ch a nc e aud name ptrs s = .ok (msg, ord))
    (hbind : bindCtx sg appTorrent (Rec.make ch (commitOf ch a n msg) ls a) (n.bytes ++ msg) = .ok ctx) :
    assembleOk ctx s = true ∧ ctx.desc.ordered = ord
theorem btBuild_binds {ch sg : GroupId} {a : Aci} {nc n : Nonce} {e : Nat}
    {aud ptrs s msg : ByteArray} {name : String} {ord ls : Array Digest}
    (hb : btBuild ch a nc e aud name ptrs s = .ok (msg, ord))
    (hch : ch = channelId sg appTorrent channelTorrent) :
    ∃ ctx, bindCtx sg appTorrent (Rec.make ch (commitOf ch a n msg) ls a) (n.bytes ++ msg) = .ok ctx
theorem run_btFile {s : State} {key name : String} {len : Nat}
    (h : run s (.file key) = .file name len) :
    ∃ ctx, s.ctxs[key]? = some ctx ∧ ctx.header.app = appTorrent ∧ ctx.desc.len = len ∧
      ctx.desc.manifest = manifestOf name len ∧ safeComponent name = true
end Zrdt.Torrent
```

### C.3 Lane git (`core/Zrdt/Git.lean`; `[M]` in `Crdt/Merkle/AppsGit.lean` and Api.lean §6c)

```lean
namespace Zrdt.Git
open AppBase
-- Objects: the id check is sound, and the raw form is an injective encoding.
theorem checkObjects_sound {s : ByteArray} {os : Array Obj} (h : checkObjects s = some os) :
    s = os.foldl (fun acc o => acc ++ o.raw) .empty ∧
    (∀ o ∈ os, o.raw = rawOf o.kind o.content ∧ o.id.bytes = (sha256 o.raw).bytes ∧
      o.wellFormed = true) ∧
    ∀ i j (hi : i < os.size) (hj : j < os.size), i < j → compare os[i].id os[j].id = .lt
theorem parseRaw_rawOf (k : Kind) (c : ByteArray) : parseRaw (rawOf k c) = some (k, c)
theorem parseBody_writeBody {b : Body} (hw : b.wellFormed = true) : parseBody (writeBody b) = some b
theorem writeBody_parseBody {x : ByteArray} {b : Body} (h : parseBody x = some b) : writeBody b = x
theorem run_git_objects {s : State} {key : String} {st : ByteArray} {os : Array Obj}
    (h : run s (.objects key st) = .objects os) :
    ∃ ctx b, s.ctxs[key]? = some ctx ∧ ctx.header.app = appGit ∧ assembleOk ctx st = true ∧
      checkObjects st = some os ∧ parseBody ctx.header.body = some b ∧ os.map (·.id) = b.oids
-- The pusher's checks; `t` is the table, `req` the request, `out` what GIT_PREPARE returns.
theorem checkPush_root {t : Table} {req : PrepareReq} {out : Prepared}
    (h : prepare t req = .ok out) (hns : req.share = false) {o : Obj} (ho : o ∈ out.objects)
    (hk : o.kind = .commit) (hp : commitParents o = []) : t.complete = true
theorem checkPush_fresh {t : Table} {req : PrepareReq} {out : Prepared}
    (h : prepare t req = .ok out) (hns : req.share = false) :
    ∀ o ∈ out.objects, ∀ e ∈ t.entries, o.id ∉ e.body.oids
theorem checkPush_gate {t : Table} {req : PrepareReq} {out : Prepared}
    (h : prepare t req = .ok out) (hns : req.share = false) :
    ∀ s ∈ checkedSeats req, (∀ x ∈ refsOut out, entitled t s x) ∧
      ∀ u ∈ req.updates, ∀ v, u.old = some v →
        ∃ e ∈ t.entries, seated e s ∧ assigns e req.repo u.name (some v)
-- G-F1 (advertised): what a non-share push may carry.
theorem checkPush_history {t : Table} {req : PrepareReq} {out : Prepared}
    (h : prepare t req = .ok out) (hns : req.share = false) :
    (∀ o ∈ out.objects, ∀ e ∈ t.entries, o.id ∉ e.body.oids) ∧
    (t.complete = false → ∀ o ∈ out.objects, o.kind = .commit → commitParents o ≠ []) ∧
    ∀ s ∈ checkedSeats req, ∀ x ∈ refsOut out, entitled t s x
theorem checkShare_exact {t : Table} {req : PrepareReq} {out : Prepared}
    (h : prepare t req = .ok out) (hs : req.share = true) :
    commitIds out = newValues req ∧ (∀ x ∈ refsOut out, x ∈ parentIds out) ∧
    out.covers = req.expect ∧ out.covers = coversOf t req out ∧
    (∀ s ∈ out.covers, keyChanged t s = false) ∧
    ∀ s ∈ checkedSeats req, s ∉ out.covers →
      ∀ o ∈ out.objects, (∃ e ∈ t.entries, o.id ∈ e.body.oids) → entitled t s o.id
-- What the view is (so refs_agree is not vacuous).
theorem pushLog_spec {t : Table} {repo : String} {x : LogEntry} :
    x ∈ (gitView t repo).log ↔ ∃ e ∈ t.entries, e.body.repo = repo ∧
      ∃ u ∈ e.body.updates, x = ⟨e.digest, e.author, e.body.share, u⟩
theorem refs_spec {t : Table} {repo n : String} {d : Digest} {v : Option Oid} :
    (n, d, v) ∈ (gitView t repo).refs ↔ ∃ e ∈ t.entries, e.digest = d ∧ assigns e repo n v ∧
      ¬ ∃ f ∈ t.entries, (∃ u ∈ f.body.updates, f.body.repo = repo ∧ u.name = n ∧ u.old = v) ∧
        d ∈ t.reach f
theorem run_git_prepare {s : State} {p : PrepareReq} {r : Reply} (h : run s (.prepare p) = r) :
    ∀ out, r = .prepared out → ∃ ch, s.chats[p.channelKey]? = some ch ∧
      prepare (tableOf ch p.helds) p = .ok out
theorem run_git_view {s : State} {sg : GroupId} {ck repo : String} {hs : Array (Digest × ByteArray)}
    {v : View} (h : run s (.view sg ck repo hs) = .view v) :
    ∃ ch, s.chats[ck]? = some ch ∧ v = gitView (tableOf ch hs) repo
end Zrdt.Git

-- [M], Crdt/Merkle/Api.lean Part 6c (they need CheckedStore.agree). `Complete c hs`: every stored
-- record has a held opening that matches it.
theorem Zrdt.Apps.refs_agree (c d : CheckedStore) (hc hd : Array (Digest × ByteArray))
    (repo : String) (h : c.heads = d.heads) (hcc : Git.Complete c hc) (hdc : Git.Complete d hd) :
    Git.gitView (Git.tableOfStore c hc) repo = Git.gitView (Git.tableOfStore d hd) repo ∨
      ∃ x y : ByteArray, x ≠ y ∧ sha256 x = sha256 y
theorem Zrdt.Apps.force_visible (c d : CheckedStore) (hc hd : Array (Digest × ByteArray))
    (repo : String) (h : c.heads = d.heads) (hcc : Git.Complete c hc) (hdc : Git.Complete d hd)
    {x : Git.LogEntry} (hx : x ∈ (Git.gitView (Git.tableOfStore c hc) repo).log) :
    x ∈ (Git.gitView (Git.tableOfStore d hd) repo).log ∨ ∃ x y : ByteArray, x ≠ y ∧ sha256 x = sha256 y
-- Stretch (deferred if it costs more than half a day): RelStore.refs_agree over RelStore.agree.
```

`refs_agree` goes through three steps:
1. `CheckedStore.agree` gives equal record sets, or a collision.
2. `opening_bound` gives equal openings.
3. A lemma in `AppsGit.lean`, `gitView_congr`, says that equal tables give equal views.

It holds only between members whose tables are complete. A newcomer's view is not covered: he
was not given the openings (G-m7).

### C.4 Advertised (Api.lean Part 6; `comparator.json` and `Comparator/Challenge.lean` at integration)

| Lane | Advertised (namespace `Zrdt.Apps`) |
|---|---|
| base | `app_not_chat`, `channelId_inj` |
| torrent | `run_piece_accept`, `pieces_follow_announcement`, `serve_pieces`, `assemble_unique`, `btBuild_complete` |
| git | `checkObjects_sound`, `checkPush_history`, `checkShare_exact`, `refs_agree`, `force_visible` |

That is 12 statements, so the advertised count goes from 27 to 39. Everything else in §C is
pinned in `Test/Axioms.lean` as a proof obligation, as `audience_bound` is today. Each
advertised statement has, in its lane's section, a satisfiable example and a rejected bad output,
as `Api.lean` has today.

## D. Lanes and file ownership

### D.1 The lanes

| Lane | Where | Branch (local) | Base |
|---|---|---|---|
| **base** (Lean) | Linux | `apps-base` | zrdt `apps` (the skeleton commit) |
| **torrent** (Lean) | Linux | `apps-torrent` | zrdt `apps` |
| **git** (Lean) | Linux | `apps-git` | zrdt `apps` |
| **transport** (fork) | Mac mini | `apps-transport` | fork `zrdt` 3eae9af |
| **torrent-ui** (fork) | Mac mini | `apps-ui` | fork `zrdt` 3eae9af |
| helper (already running) | Linux | `apps-helper` | zrdt 22c65a3 |

Each lane works in its own worktree:
- Linux: `git -C /home/kejace/devel/zrdt worktree add <path> -b <branch> apps`.
- Mac: `git -C ~/devel/sd-jfix worktree add <path> -b <branch> zrdt/zrdt`.

Only the integration step merges lanes into `apps` and pushes, and only the branch `apps`.

### D.2 Ownership

A file listed for one lane is edited only by that lane. A **shared file** is edited only between
the lane's `[BEGIN lane <x>]` and `[END lane <x>]` markers, which the skeleton placed. Anything
not listed belongs to lane base in zrdt and to lane transport in the fork, and other lanes ask
them for changes.

| Lane | zrdt files it owns | Its sections in shared files |
|---|---|---|
| **base** | `core/Zrdt/AppBase.lean` (and new `core/Zrdt/AppBase/*.lean` if it splits), `core/Zrdt/Apps.lean` (dispatcher, guard, build id), `Crdt/Merkle/AppsBase.lean`. The protocol-5 lines outside the markers of `Proto.lean` (`Code`, the status table, `protocolVersion`, `opName?`); `core/Zrdtd/*`, `core/Zrdt.lean`, `vectors/zrdtd_client.py`. At integration: `comparator.json`, `Comparator/Challenge.lean`, `README.md`, `Makefile`, `docs/apps/` | `Proto.lean`: `[lane base]` in the header (field types and base layouts) and in the op names (`baseOpNames`). `Vectors.lean`: `[lane base]` sessions (`baseSessions`, `baseUncovered`) and checks. `Api.lean`: Part 6a. `Test/Axioms.lean`: `[lane base]` |
| **torrent** | `core/Zrdt/Torrent.lean`, `core/Zrdt/PieceProofs.lean`, `Crdt/Merkle/AppsTorrent.lean` | `[lane torrent]` in each of the same four files: `torrentOpNames`, `torrentSessions`, `torrentUncovered`, Part 6b |
| **git** | `core/Zrdt/Git.lean` (and new `core/Zrdt/Git/*.lean`), `Crdt/Merkle/AppsGit.lean` | `[lane git]` in each of the same four files: `gitOpNames`, `gitSessions`, `gitUncovered`, Part 6c |
| helper | `tools/` (`tools/git-remote-zrdt/` with `ENDPOINT.md`, `tools/git-zrdt/`) | none |

| Lane | fork files it owns |
|---|---|
| **transport** | `protos/SignalService.proto` (Content 205, `ZrdtPointers`, `ZrdtServeRequest` 7-8, `ZrdtServed` 5). The protocol-5 codec and backend: `ts/zrdt/backends/{codec.std,daemon.node,stub.node}.ts`, `ts/zrdt/ZrdtBackend.std.ts`. The hooks into existing receive and serve paths, kept to calls into `ts/zrdt/apps/`: `ts/zrdt/{receive.preload,served.preload,serveRequests.std,serveArgs.std,wire.std}.ts`. New: `ts/zrdt/apps/{api.std,appMessage.std,channels.std,publish.preload,cdn.preload,pieces.std,repair.std,endpoint.node,gitRoutes.std,gitFetch.std,demoHooks.std}.ts` and their `_test` files. In `demo/`: `evil.ts` (CDN delete, download corruption, withhold), `harness.ts` (group "Code", add a member during a beat), `launch.ts` (the endpoint file per desktop). Updating the zrdt submodule at integration |
| **torrent-ui** | `ts/zrdt/apps/bt/{manager.std,routes.std,write.node}.ts`, `ts/zrdt/apps/ui/*.dom.tsx` (share dialogs for both apps, the torrent and git status, the "failed its check" notice), `tools/zbt/` (CLI), `demo/beats/{torrent,git}.ts`, `demo/smoke-apps.ts`, `demo/DEMO.md` (an apps section), the `smoke-apps` target in the top-level `Makefile` |

**Interfaces between lanes.**
- **Lean lanes.** They share only `Zrdt.AppBase` and the dispatcher hooks, which the skeleton
  fixed:
  - `Torrent.parse`, `Torrent.run : State → Request → Reply` (read-only);
  - `Git.parse`, `Git.run` (read-only);
  - `AppBase.parse`, `AppBase.run : State → Request → Reply × State`.

  Lanes torrent and git never edit `AppBase.lean` or `Apps.lean`. A change to a shared
  definition or layout goes through lane base and is announced to the other lanes.
- **Imports run one way.** `AppBase` imports `Proto`. `Torrent` and `Git` import `AppBase`.
  `Apps` imports all three, and `PieceProofs` imports `Apps`. The `Crdt/Merkle/Apps*.lean` files
  import their core modules and never `Api.lean`. `Api.lean` imports all three; its Part 6
  sections may use earlier statements of `Api.lean` (git's `refs_agree` uses
  `CheckedStore.agree`).
- **Fork lanes.**
  - torrent-ui codes against `ts/zrdt/apps/api.std.ts`, which transport writes first (day 0.5):
    `openChannel`, `publish`, `fetchPieces`, `repairStatus`, and `registerRoutes` on the
    endpoint. Until it exists, torrent-ui uses a fake.
  - The git helper codes against ENDPOINT.md.
  - Both fork lanes code against §B, and against the TS stub replaying `vectors.json` from zrdt
    `apps` once the Lean lanes' sessions land.

### D.3 Collision rules

- **Markers.** A lane changes no line outside its own markers in a shared file. The integrator
  checks this with `git diff apps...<lane> -- core/Zrdt/Proto.lean core/Zrdt/Vectors.lean
  Crdt/Merkle/Api.lean Test/Axioms.lean`.
- **Generated files.** `vectors/vectors.json` is generated. Lanes do not commit it; the
  integrator runs `make vectors` once after the merges.
- **Line endings.** Line endings and indentation outside a lane's sections stay byte-identical,
  so `git merge` takes the three lanes without conflict.

## E. Gates

### E.1 Stage 1 (zrdt, Linux; integration on `apps`)

1. **Builds.** `lake build` (root) and `cd core && lake build` pass, every
   `lake build` and `make` wrapped in
   `systemd-run --user --scope -q -p MemoryMax=16G -p MemorySwapMax=0 -- <cmd>`.
2. **Axiom gate.** `Test/Axioms.lean` pins every theorem of §C to `propext`,
   `Classical.choice` and `Quot.sound` or fewer. There is no `sorry`, `admit`, `native_decide` or
   new axiom.
3. **Closure.** `make closure` is silent: `zrdtd` stays Mathlib-free.
4. **Vectors.** `make vectors && make run` pass:
   - **Protocol-4 sessions.** The 7 sessions are unchanged, except `VERSION` (4 → 5, switched by
     lane base when its ops land) and the fuzz step "op 0x30" (it was 0x17).
   - **New sessions.** `pieces` (base), `torrent` and `git`.
   - **Coverage.** Every protocol-5 op appears in some session. The three `uncovered` lists are
     empty, so every status except `COLLISION` appears.
   - **The beats at the frame level, with k = 10.**
     - Torrent: build, bind, accept, three pieces missing, a tampered repair entry →
       `BAD_PIECE`, a good one → `OK`, `PIECES_COMPLETE` `OK`, `ASSEMBLE` `OK`.
     - Git: P1, forced P2, three equal `GIT_VIEW`s (one channel key per member), Dave's
       relative store, `GATE`, S (`COVERS_CHANGED`, then `OK`), P3, `ROOT` for a newcomer's root
       push, and `OLD_OBJECT` for a re-push.
5. **Examples.** Each advertised statement has a satisfiable example and a rejected bad output.
6. **Untouched files.** `git diff origin/main -- core/Zrdt/{Digest,Sha256,Record,Encode,Store,RelStore,
   Provenance,Commit,Serve,ChatStore}.lean Crdt/Merkle/` lists only `Api.lean` (imports and
   Part 6) and the new `Apps*.lean`. In `Proto.lean`, `git diff origin/main` (22c65a3) touches only:
   - the status rows and the protocol-5 header section;
   - `Code` and its tables;
   - the op-name sections and `opName?`;
   - three `#guard` lines and `protocolVersion`.

   No protocol-4 code path changes.
7. **No skeleton text left.** `grep -rn -e "Not yet written" -e "Empty in the skeleton" -e
   "skeleton has no op yet" core/Zrdt Crdt Test` is empty.
8. **Comparator files.** `comparator.json` and `Comparator/Challenge.lean` gain the 12
   advertised statements (27 → 39), and the README and Makefile counts follow. **Comparator,
   `lake check`, leanchecker and `make check` are not run.** They come last, and only with
   kejace's approval.

### E.2 Stage 2 (fork, Mac mini)

9. **Smoke.** `demo/smoke-apps.ts` passes both beats of §A with the real protocol-5 `zrdtd`,
   with one check per step. Before running, check
   `pgrep -fl 'demo/(smoke|launch|beat)|run-demo'` and wait if another run is going. Use the
   assigned panel port.
10. **No regression.** The base branch's smoke still passes (GO 77/77), and the TS stub replays
    the new `vectors.json` byte for byte.
11. **Endpoint.** The git helper's own tests pass against the fork's endpoint. This is the
    ENDPOINT.md alignment.
12. **Rehearsal.** One rehearsal of both beats, recorded in `demo/DEMO.md`.

## F. Order and effort (agent-days, in parallel)

**Stage 1 (Lean), about 4 days.**
- **base:**
  - the six base ops and their layouts in `Proto.lean`: 1.5;
  - the guard lemmas and `run_channel`: 0.5;
  - the §C.1 encoding and separation proofs: 1.5;
  - integration: 0.5.
- **torrent:**
  - `pieceOk_unique`, `bindCtx_unique`, `assemble_unique` on the skeleton's definitions, from
    now: 1;
  - `BT_BUILD`, `BT_FILE`, `safeComponent` and the torrent session: 1;
  - once base's ops land (about day 1.5): `run_*`, `PiecesInv`, `pieces_follow_announcement`,
    `serve_pieces`: 1.5.
- **git:**
  - objects and `checkObjects`: 1;
  - the body, the table and the checks: 1.5;
  - the view: 0.5;
  - the `Api.lean` §6c proofs: 0.5;
  - the beat session: 0.5.

**Stage 2 (fork), about 7.5 days, starting at once against §B and fakes.**
- **transport:**
  - `api.std.ts` first: 0.5;
  - protos and the codec: 0.5;
  - channels and Content 205: 1;
  - publish and CDN: 1;
  - pieces: 0.5;
  - repair: 1;
  - the endpoint and the git routes: 1;
  - evil and harness: 0.5.
- **torrent-ui:**
  - the torrent manager, `zbt` and writes: 1.5;
  - dialogs and notices: 1;
  - the beats and `smoke-apps.ts`: 1.5.
- **Then together:** the smoke on the real `zrdtd` (1), and a rehearsal (0.5).

## G. Deferred (written down)

- **Torrent:**
  - folders: a file table, with names refused when they collide after NFC and case folding
    (T-M5);
  - pieces of 4 to 64 MiB and N up to 4096, with a separate piece list;
  - on-demand mode, `.torrent` export, the midstate op, deduplication and re-sharing;
  - persisted piece stores;
  - repair budgets and the `queued`/`cancel` frames (T-M3's rest);
  - T-m1 to T-m4 and T-m6 to T-m9.
- **Git:**
  - the receivers' audit (audit mode, `VIOLATION`/`UNKNOWN`, `checkPush_objective`; G-M4,
    G-M5);
  - provenance-aware entitlement and the log's provenance labels (G-m10);
  - chains beyond 512 objects;
  - packs, repack, annotated tags and notes (G-m11);
  - a verified-key override for `KEY_CHANGED`;
  - strict sharing, and sharing history (a newcomer cannot push a multi-commit history with a
    root, and creates a new repository only as a one-commit share);
  - a Lean ancestry check of `forced`;
  - padding (G-m2);
  - warnings about commit ids in messages;
  - `RelStore.refs_agree`, if it is not done as the stretch;
  - G-m1, G-m3, G-m6, G-m8 (moot with one channel per group, except that git is in use) and
    G-m12;
  - SHA-1 repositories: out, by user decision.
- **Transport:**
  - the own-device copy of Content 205;
  - the official-server profile and pacer;
  - `BAD_APP` at accept time;
  - epochs and pruning, and CDN-expiry refresh;
  - TRANSPORT's blobs, carriers, via rule and `GRANTS` (dropped by the user decision).

## H. Trusted base and honest limits of M1

**Trusted, beyond the README's list:**
- the git object parser (Lean, not proved against git; pinned by vectors from real SHA-256
  repositories), like today's protobuf scan;
- `git hash-object` on the receiver: it recomputes the id and the helper compares, so a failure
  there only refuses;
- **the host's duties:**
  - upload exactly the stream's slices, with fresh keys;
  - pass field 205 as received to `COMMIT`;
  - keep app openings for good;
  - send to recipients ⊆ seats;
  - never let the sendLog retry Content 205;
  - re-check members and keys at freeze;
  - share only from the fork's dialog;
  - write only checked bytes;
  - extract (i, bytes) from repair openings (a mistake there only refuses).

M1 adds no zlib in Lean, no new crypto, no signature and no new axiom.

**Git (R1) holds at the pusher's `zrdtd`, against host bugs and the server.** It does not hold
against:
- **A modified client.** It can still paste. There is no audit until M2.
- **Objects from outside the channel.** Freshness is relative to the pusher's table, so these
  count as fresh. Edited copies of old content are missed too.
- **An incomplete table that re-sends non-root history.** A member whose relative store lacks a
  record R (key change, lost device) still has an old clone. He can push old commits that R
  carried, if they sit on a tip the checked seats are entitled to. Freshness cannot see R, and
  the root rule does not apply. Only the receivers' audit (M2) names it. The helper warns when a
  push from a relative store carries commits older than the store's join.
- **Inflated entitlement.** The table believes every git record's claims. A member, or a record
  relayed in his name, can claim to carry objects. Later honest pushes may then name those ids
  to a newcomer, without their content.

**Also:**
- A newcomer learns a shared commit's parent ids.
- A member whose key changed blocks pushes until he is removed.
- Each call passes every opening of the channel, a demo-size cost.
- The server can withhold a push from one member (`withheld_tail_undetectable`); his compare
  code then differs, which is visible.

**Torrent.** A newcomer sees older announcements only as digests: never names, sizes, store ids
or bytes. The server sees sizes, timing, uploaders, and who repairs for whom. It can delay or
withhold.

## I. Critique pass: what a skeptic's reading of the draft changed

1. **G-F1 was half-open.**
   - **Problem.** The draft had one git channel per repository name. A second repository name
     starts from an empty table, so "first push into an empty store" let anyone re-send any
     history there, guarded only by a helper flag.
   - **Fix.** There is now one git channel per Signal group (the repository name is in the
     body). The root rule asks for a complete table, of which "empty" is a special case. So
     founders can still create new repositories with history, and incomplete tables cannot
     re-send a root. `checkPush_history` states the result.
2. **The author's store was special.**
   - **Problem.** The author's piece store came from `BT_BUILD`'s inputs, so
     `pieces_follow_announcement` had an author case, and a host mismatch made a store
     unfetchable. `assemble_unique` did not relate the author to a receiver.
   - **Fix.** `BT_BUILD` and `GIT_PREPARE` are now pure. Every store comes from `PIECES_BIND` of
     an accepted A. Only base's ops write state, so `PiecesInv` covers three ops and `CLOSE`.
3. **F was carried, with checks that could fail.**
   - **Problem.** F's record and opening were inline, with "F's 201 = A's 201" and "F's opening
     matches" checks.
   - **Fix.** F is now derived from A's audience and descriptor. The mismatch cannot happen.
4. **Ops the guarantees do not need were dropped.**
   - `APP_MESSAGE`: `BT_BUILD` and `GIT_PREPARE` return the message, so the host never builds
     one.
   - `PIECE_VIEW`: `PIECE_ACCEPT` recomputes everything from (i, bytes), so the requester's
     extraction is untrusted.
5. **The channel binding was a host duty.**
   - **Problem.** Nothing checked that a record's committed app and channel name are its
     channel's.
   - **Fix.** `bindCtx` and the git ops now check `channelId(sg, app, name)` = A's group
     (`channelId_inj` makes it meaningful).
6. **Vacuity.**
   - `refs_agree` "with equal heads" is false for structure-only records, and vacuous for a
     constant view. It now needs `Complete` on both sides, and `pushLog_spec` and `refs_spec`
     pin the view.
   - `checkPush_root` is not vacuous: the vectors hold both an `OK` root push (complete table)
     and a `ROOT` refusal.
7. **Overclaims removed.**
   - "The villain tampers and is caught": the server is caught by Signal's MAC, and members by
     zrdt.
   - The torrent "code equals" adds nothing beyond A.
   - A newcomer's equal code does not mean an equal view.
   - "Forced" is a flag, not a checked fact.
8. **Pieces missing for the beats, now planned:**
   - Dave must hold piece 7 to tamper with it, so he fetches at step 2.
   - Every 1 MiB repair reply exceeds 48 KiB, so `sealedOnCdn` is on the critical path.
   - The harness needs group "Code" and an add-member step.
   - The evil server needs delete and corrupt hooks.
   - The receiver's `COMMIT` needs the exact field-205 bytes.
   - `git clone` needs HEAD.
   - Vectors cannot carry 1 MiB pieces, so k = 10 is allowed for tests.
9. **Ownership.** The draft's `Proto5.lean` and its unmarked shared files would have made three
   Lean lanes edit the same lines. Now:
   - the dispatcher's hooks are wired in the skeleton;
   - all statuses are fixed;
   - every shared file has marked lane sections;
   - torrent and git never touch base's files.
10. **Checked and clear:**
    - no zlib and no idx in Lean;
    - the only new trusted code is the object parser and the tree and commit grammar;
    - no theorem needs an axiom;
    - every advertised statement has a planned satisfiable instance;
    - no statement above is known to be false of the skeleton's definitions (the skeleton's
      `#guard`s exercise `assembleOk`, `pieceOk`, the descriptor round trip and tag separation
      at k = 10).
