# GIT_PLAN: sharing a git repository over Signal + zrdt

Status: design, 2026-11-01. Not implemented. Built on `docs/apps/TRANSPORT.md` (this worktree,
branch `apps`) and JOIN_PLAN v2 (branch `join`). Nothing here changes the demo build. Written by
the git judge from two competing designs (§7) and the two fact checks (Signal as a transport; git
and BitTorrent protocols).

> **Status (2026-11-01): design only, no code.** The adversarial review ran after this was
> written, but its findings are **not yet folded in**: they are listed, open, in the last section,
> "Open issues from the adversarial review" (1 fatal, 7 major, 13 minor). Read that
> section before trusting any claim below.
>
> **Protocol caveat.** Written against join `acbd70a` (frame protocol 3). join is now `9637904`,
> protocol 4: `ACCEPT` always takes the opening; `ACCEPT_VIEW` has a mode (catch-up or
> per-digest) and a pending list, and in per-digest mode admits only linked boundary digests;
> `MERGE` carries audiences. JOIN is also now built in both repos (JOIN_PLAN header: zrdt draft PR
> l-adic/zrdt#3, fork draft PR l-adic/signal-desktop-zrdt#7), and join `00c9b96` adds the
> relative-store restatements (`agree_rel`, `serve_content`, `serve_content_complete` for a store
> with a boundary). So statements below that JOIN's fork stages are not started, or that the
> relative restatements are pending, are out of date. Op numbers, frame layouts and cited line
> numbers need re-checking against protocol 4 before building.

## 0. For a reviewer starting cold

**What this is.** The git app on top of the zrdt transport. Members of a Signal group push to and
fetch from a remote `zrdt::<group>/<repo>`. There is no git server. Each push is one zrdt record.
The data is a git pack, carried as a transport blob on Signal's CDN. `zrdtd` (Lean) recomputes
every git object id in the pack and checks the push before anyone sends it.

**The design in eight lines.**
1. **One channel per repository**: (Signal group, app tag, repo name), as TRANSPORT §2. The app
   tag fixes the object format: `git-sha256` first, `git` (SHA-1) in a later stage.
2. **One push is one record.** Its committed body is a push header: the exact commit ids the pack
   carries, their outside parents, the ref updates, and a share flag. The bulk is a raw git pack
   (not thin), carried as one blob. **No git bundle file goes on the wire.**
3. **Lean checks the objects.** `CHECK_PACK` hashes every object and checks that the pack holds
   exactly the committed commits plus objects of their trees, with no signatures.
4. **Lean checks the push.** `CHECK_PUSH`, at freeze, checks three things: no commit leaves again
   unless the push declares it a share; every seated account already has the history the push
   builds on (the **gate**); and refs name nothing a seated account was not given.
5. **Refs are a multi-value register** over the record graph. Concurrent pushes both get `ok`, and
   both values show until someone merges. Members with equal heads see equal refs (proved).
6. **A newcomer gets nothing older** until a member deliberately shares. A share is a committed
   flag, shown to everyone. It gives the shared commit and its tree as a shallow cut, never its
   history.
7. **No signatures.** Signed commits, signed tags and push certificates are refused. "Pushed by"
   is the record's author, authenticated deniably by Signal.
8. **The fork does the work.** A per-channel bare mirror holds the checked packs. The helper
   `git-remote-zrdt` is thin: it talks to the fork and fetches from the mirror.

**Read, in this order.** TRANSPORT.md §0–§5 (channels, app messages, blobs, carriers, the via
rule). JOIN_PLAN §3, §5, §6 (audience, `SERVE`, relative stores). Then this document. §7 says what
each competing design proposed and what was kept.

**Scores** (out of 10; how each design meets the criteria the workflow set).

| Design | Security (R1–R3, server) | Provability | Fit with zrdt and Signal | User value | Overall |
|---|---|---|---|---|---|
| D1 `git-remote-zrdt`: bundles as blobs, Lean checks lists, `COVERS` | 6 | 6 | 6 | 7.5 | 6.5 |
| D2 `zgit`: raw packs, Lean checks objects, the gate | 8.5 | 8 | 7.5 | 6 | 7.5 |

- **D1.** It has a good server model, a clean ref register (proved in scratch, the same under all
  120 orders of five records), and SHA-1 support. But its R1 rests on object lists that the host
  reads from git output; Lean never sees an object. Its `COVERS` check counts only
  *participants*. Seated members who never used the repo still receive the bundle, and with it new
  trees that name older files, older commit ids, and the subject lines of older commits (git writes
  them into the bundle header; D1's own log shows `-430d2fa3… e2`). Its helper is a Lean binary
  that needs a C shim to reach a Unix socket.
- **D2.** R1 and R2 for git become theorems about `zrdtd`. Every seated account counts. The bundle
  leak and the range-merge leak are closed by construction. Weak points: it handles SHA-256
  repositories only (no existing repositories, little host support). Deleting an old branch still
  revealed its name. Cuts were found by a heuristic. All checks ran on the pusher's side.
- **Verdict.** D2 is the base. From D1 this plan takes SHA-1 channels, the causal ref register
  with its proofs, the forced flag and its audit, Lean-rendered helper lines, `shadowed`, and the
  regression tests. New here: the name rule, the gate over the causal past (so every member can
  audit it), cuts only from share records, the pack header and trailer bound to the committed root,
  and the mirror's packs used as the pinned bytes. Details are in §7.

**Checked in this session** (by the judge, in addition to the designers' checks):
- Both scratch Lean files compile again with `lake env lean` (v4.35.0, core at `join`), with no
  `sorry`. D2's four lemmas use only `propext`, `Quot.sound`, and (for the two pack lemmas)
  `Classical.choice`. Copies and outputs: `/tmp/zrdt-apps-gitjudge/lean/`.
- `/tmp/zrdt-apps-gitjudge/scripts/mirror_check.sh` (git 2.43.0, SHA-256 repositories):
  - `git index-pack --stdin` stores a non-thin pack byte for byte, so a mirror's pack file *is*
    the record's blob (§2.9);
  - a plain `git fetch` from a shallow mirror is refused ("shallow roots are not allowed to be
    updated"), and `--update-shallow` accepts it, so the documented path works (§2.7).
- D1's log (`/tmp/zrdt-apps-git1/r1_exclusion.log`) shows git writing prerequisite subjects
  (`-dfe1b5d6… c3`, `-430d2fa3… e2`) into bundle headers. D2 saw the same in a SHA-256 v3 bundle.

## 1. What the user gets

A small team that already talks in a Signal group can share a git repository with no server.
Each member adds a remote (`git remote add team zrdt::team/repo`) and uses `git push`, `git fetch`
and `git pull` as usual. Signal carries everything end-to-end encrypted. The server sees only
padded blobs, their sizes, and their timing. Every push is checked, so a pack that does not match
what its pusher committed is refused and blamed on that pusher. Members whose stores have the same
heads see the same branches (a theorem, plus a compare code they can read to each other). A
member added later gets nothing from before he joined unless someone deliberately shares it, and
the code that enforces this is proved. Nobody needs commit signatures; authorship comes from
Signal, deniably. It suits small, private, offline-tolerant collaboration (journalists, activists,
small labs) more than large or public projects. It is not a git server: there are no hooks, no
central branch order, and no pull requests (§5).

## 2. The design

### 2.1 Place in the stack

- **JOIN v2:** the audience in field 201, `SERVE`, the seal, relative stores for newcomers.
- **TRANSPORT:** channels, Content 205, the app body (field 212) and blob references (field 213),
  pieces and carriers, the via rule, re-upload requests, the pacer, the socket API.
- **This app** adds:
  - a body schema;
  - a git table per channel in `zrdtd`;
  - the ops `GIT_BODY`, `CHECK_PACK`, `CHECK_PUSH`, `GIT_REFS` and `GIT_HAS`;
  - a mirror per channel in the fork;
  - the helper `git-remote-zrdt`.

  All the Lean is Mathlib-free, in `core/Zrdt/Git/`.

### 2.2 Channel, URL, object format

- **URL:** `zrdt::<group-alias>/<repo>`. The fork resolves the alias to a Signal group id.
- **Channel:** `open(group, app, repo)`. `app = "git-sha256"` for SHA-256 repositories, or
  `"git"` for SHA-1 ones (stage G6). The channel id hashes the tag, so the two formats never mix,
  and a mismatched repository is refused when it is opened.
- **Why SHA-256 first:** git ids are then 32-byte values of zrdt's `Digest` type. `zrdtd`
  recomputes them with the SHA-256 it already ships; D2 checked this with `#guard` against
  `git rev-parse` for a commit, a tree and a blob.
- **Why SHA-1 later:** every existing repository, and most hosts, use SHA-1 (it is still git's
  default through 2.56). It needs a Lean SHA-1, and on those channels the object-level theorems
  read "or a SHA-1 collision" (§3.3).
- **Audience:** the Signal group's members (TRANSPORT §2). There is no per-branch access control.
  To share with fewer people, use a smaller Signal group.

### 2.3 One push, one record

The body is field 212: at most 32 KiB, canonical, parsed strictly by Lean (`GitBody`). Numbers are
big-endian. An oid is 32 bytes (`git-sha256`) or 20 bytes (`git`).

```
GitBody = "zgit1" ‖ flags u8                 bit 0: share (deliberate, §2.8); other bits 0
        ‖ u16 nC ‖ nC × oid                  commits K the pack carries, strictly increasing, ≤ 512
        ‖ u16 nS ‖ nS × oid                  shares ⊆ K: older commits carried again on purpose
        ‖ u16 nP ‖ nP × oid                  prereqs = parents(K) \ K, exactly, increasing
        ‖ u8 nU ‖ nU × update                sorted by name, distinct, ≤ 64
update  = u8 len ‖ name ‖ op u8 ‖ value ‖ forced u8
          op 0 set (value = oid) | 1 delete (no value) | 2 HEAD symref (value = u8 len ‖ refs/heads/ name)
```

- **Blobs.** Field 213 holds exactly one data BlobRef (the pack) iff nC > 0, and nothing otherwise.
  A body with no pack is a pure ref move or delete.
- **Consistency rules:**
  - shares ≠ ∅ implies the share flag;
  - nU = 0 only if nC > 0 (the earlier records of a chain).
- **Ref names** (`validRefName`):
  - the name starts `refs/heads/`, `refs/tags/` or `refs/notes/`, or is `HEAD` for op 2;
  - no empty component, and none starting with `.` or ending in `.lock`;
  - no `..`, `@{`, `//`, and no trailing `/` or `.`;
  - no byte ≤ 0x20, no 0x7f, none of `~^:?*[\`;
  - at most 255 bytes;
  - refused: `refs/zrdt/*`, and any name containing `.zrdt-` (reserved for presentation, §2.5).
- **Large pushes** are chains. More than 512 commits become records of at most 512 each. Each
  record links the one before (the author holds it) and lists that record's commits among its
  prereqs. Ref updates go in the last record only, so `--atomic` holds. Taken from D2: the table
  stays a function of openings alone, which keeps `refs_agree` simple. (D1 put long lists in a
  second blob instead; that makes the table wait for a download.)
- **No bundle file**, for four reasons:
  1. `git bundle create` writes `-<oid> <subject of that commit>` for every prerequisite, which is
     an older commit's message (verified by both designers);
  2. a bundle cannot express a shallow cut (fact check B);
  3. bundles use range semantics (`^P tip`), which ship side-branch commits on a merge (verified:
     `^C4 M` ships "feature: pre-join secret work");
  4. the header would only repeat the committed body.

  A receiver can rebuild a standard bundle locally if some tool wants one.

### 2.4 What `zrdtd` checks

**The git table** (per git channel, in the app section of `zrdtS4`):
- It maps a record digest to (author, K, shares, prereqs, updates, flag). Audiences come from
  JOIN's audience table.
- It is filled only by `ACCEPT`, `ACCEPT_RECORD` and `ACCEPT_VIEW`, from an opening `zrdtd` has
  checked, as JOIN fills the audience table. Git channels keep their openings.
- `run_accept_git` says the entry is exactly the opening's body. A body that fails `GIT_BODY` makes
  the accept reply `BAD_APP`.

**Entitled.** Account `a` under key tag `t` is entitled to commit `c` if some record in the table
lists `c` in K and its own committed audience seats `a` with tag `t` (t ≠ 0). This is JOIN's
`seats`, applied to commits. A member whose key changed is not entitled, exactly as `SERVE` would
treat him.

**`CHECK_PACK`** is a session: `BEGIN`, then `OBJ` × N, then `END`.
- **`BEGIN`** takes:
  - the record's BlobRef;
  - the pack's 12-byte header and its 32- or 20-byte trailer, each with a Merkle proof against
    the committed root, as `CHECK_PIECE` does;
  - the `.idx` bytes.
- **`OBJ`** takes one object (kind, content), in idx order, chunked.
- **`END`** returns `OK`, or `BAD_PACK` with a reason.
- **It checks:**
  - the idx's pack checksum equals the trailer, and the idx count equals the header count;
  - the i-th streamed object's `gitOid` equals the i-th idx id, and exactly N objects arrive, so
    the host cannot leave one out;
  - the pack's commits are exactly K, and prereqs = parents(K) \ K;
  - **rooted:** every tree is the root tree of a K commit or an entry of a pack tree, and every
    blob is an entry of a pack tree. Gitlinks (mode 160000) are never followed;
  - **unsigned:** no `gpgsig`, `gpgsig-sha256` or `mergetag` header, and no tag object (v1 has
    lightweight tags only).

**`CHECK_PUSH`** takes the frozen field-201 bytes, the author, the links and the body. Mode
`publish` runs at enqueue and at freeze; mode `audit` runs at every receiver. It evaluates
everything **over the causal past**: the table restricted to the records that the new record's
links reach. So its answer depends only on the record and what it reaches, and every member that
holds those openings computes the same answer (`checkPush_objective`). A pusher with a relative
store links only some of its heads (JOIN §6.2); counting the rest could pass a push that auditors
would fail.
- **Fresh:** every c ∈ K \ shares is in no K of the causal past. →`OLD_COMMIT`
- **Gate:** unless the share flag is set, for every seat s of the new audience with a non-zero tag
  and s.aci ≠ author, s is entitled to every prereq. →`GATE` (accounts, commits)
- **Refs:**
  - *target rule:* a set value is in K, or every such seat is entitled to it;
  - *name rule:* if the causal past assigns name n, every such seat is seated, with the same tag,
    in some record there that assigns n, unless the share flag is set. It stops a delete or update
    from revealing the name of a branch a newcomer never saw (a gap in D2).

  →`BAD_REF`

**`GIT_REFS`** returns the ref view (§2.5). Given the set of records the host has applied, it also
returns the helper's `list` lines, rendered by Lean (`listLine_parse`).

**`GIT_HAS`**(aci, key) returns the commits that account is entitled to. The host uses it to plan
packs; it is for efficiency only.

### 2.5 Refs: a multi-value register

The semantics are D1's, checked in its scratch `RefMvr.lean`.
- **Assignment:** (record d, name n, value, forced), from a table entry.
- **Live values of n:** the assignments to n that no assignment to n reaches strictly through links.
  - Supersession comes from causality alone. A push that saw a value and assigned the same name
    replaces it.
  - Concurrent pushes stay both live. A merge push links both and resolves them.
  - A delete is a value. A name whose live values are all deletes is not listed.
- **It converges.** The view is a function of the stored records and their matching openings, so
  members with equal heads (and the same openings) see equal live sets (`refs_agree`).
- **refLog:** every assignment, with its author, its forced flag, and what superseded it. It only
  grows (`refLog_mono`), so a force push and what it replaced stay visible (`force_visible`).
- **Forced flag.** It is committed. The helper refuses a non-fast-forward without `+` or
  `--force`. Every receiver that holds the objects checks with git that a non-forced update
  descends from every value it supersedes. If not, it reports "Alice's update of main dropped
  commits without marking a force". The report is attributable.
- **`shadowed(n)`:** a structure-only record (an `after` entry, JOIN §6.4) strictly reaches a live
  value of n. The helper prints "main may be out of date: 1 later record by Carol was not sent to
  you".
- **Presentation** (host, deterministic for a given live set):
  - drop a value that is a git ancestor of another live value when both are applied;
  - if one value remains, list it as `refs/heads/n`;
  - if several remain, list the smallest record digest's value as `refs/heads/n` and each other as
    `refs/heads/n.zrdt-<12 hex of its record digest>`, with a notice on stderr.

  The extra names show up as `origin/main.zrdt-…` and can be merged with plain git. Unlike D1's
  choice, which depended on the viewer's local branch, every member sees the same names.

### 2.6 Push

What runs where: git calls the helper; the helper calls the fork; the fork calls `zrdtd`.

1. **List.** git sends `capabilities` (the helper offers `fetch`, `push`, `option`, and
   `object-format` on SHA-256 channels), then `list for-push`. The helper prints `GIT_REFS` lines.
2. **Per ref.** For each `push [+]src:dst`, and for each live value v of dst:
   - v absent locally: `error dst fetch first`;
   - v not an ancestor of src, and neither `+` nor `option force`: `error dst non-fast forward`.
     These are git's exact strings.
3. **Plan** (host, for efficiency; Lean re-checks everything that matters).
   - **Commits:** K = `git rev-list <tips> --not <every table commit present locally>`, plus the
     shares from `-o zrdt.share=<rev>`.
   - **Base:** P' = the prereqs every seated account is entitled to (`GIT_HAS`).
   - **Objects:** `git rev-list --objects --no-walk K` minus `git rev-list --objects --no-walk P'`.
     With the share flag, subtract only what every seat is entitled to.
   - **Never a walking range:** it would reach the cut parents.
   - **More than 512 commits:** a chain (§2.3).
4. **Pack.** `git pack-objects --stdout` over that list, without `--thin`. D2 checked that it gives
   exactly the listed objects.
5. **Publish** (fork): `publish(channel, body, [pack])` with the git checks:
   - `index-pack` in a quarantine directory;
   - stream every idx entry (`git cat-file --batch`) into `CHECK_PACK`;
   - `CHECK_PUSH` at enqueue, as a cheap pre-check;
   - upload the pieces (TRANSPORT §5.1);
   - at freeze, `CHECK_PUSH` again with the frozen audience, then `COMMIT`, `ACCEPT` (which fills
     the table), and send;
   - put the pack into the mirror with a `.keep` file.

   On `GATE`, `OLD_COMMIT` or `BAD_REF` nothing is sent. The uploaded pieces stay orphaned, since
   their keys never left the device.
6. **Reply.** The helper answers:
   - `ok dst`, meaning *published*: accepted locally and handed to Signal. It does not mean "won
     the race";
   - or `error dst zrdt: <reason>`, for example "Bob has not been given the history this push
     builds on; push with -o zrdt.share-tree, or run git zrdt share-base main".

   On stderr: the record digest, how many members it reached, and that `ok` is not a lock.
7. **Options:**
   - `atomic`: one record, or the updates in the chain's last record; more than 64 refs is refused;
   - `dry-run`: run everything, publish nothing;
   - `push-option`: carries `zrdt.*`;
   - `pushcert`: `unsupported`;
   - signed commits are refused (`BAD_PACK`), with a hint to re-commit without
     `commit.gpgsign`.

### 2.7 Receive and fetch

**The fork applies records in accept order** to the channel's bare mirror. For each git record r:
1. **Prereqs first.** Each prereq is applied from the record that carries it. If no held record
   carries a prereq and r has no share flag, that is a gap: request it (per-digest `SERVE`, then
   pieces). If the gap cannot be closed, r's author pushed past the gate; report it ("Carol's push
   builds on history you were not given"). **Cuts come only from share records**, never from a
   heuristic.
2. **Get the pack.** Download it eagerly up to 16 MiB, otherwise on demand. Each piece passes
   `CHECK_PIECE` and goes into `via(r)` (transport).
3. **Check it.** `index-pack` in quarantine, then `CHECK_PACK`, then move the pack and idx into the
   mirror with a `.keep` file.
4. **Cut.** If r has the share flag, write the mirror's `shallow` file for each K commit whose
   parents are absent.
5. **Mark.** Set the mirror refs `refs/zrdt/r/<digest>/<i>` and mark r applied.
6. **Audit.** Run `CHECK_PUSH` in audit mode over r's causal past, plus the forced-flag audit.
   Failures become warnings attributed to r's author: live, or relayed until confirmed (A8). They
   do not block applying r, because the bytes have already arrived.

A bad pack is never imported. It is reported as "bad push by Alice (record 3f2a…)".

**The helper:**
- **`list`:** prints `GIT_REFS` lines for the values whose records are applied, plus
  `@refs/heads/<x> HEAD` and, on SHA-256 channels, `:object-format sha256`. Values still waiting are
  named on stderr ("main → 9c1d…: waiting for 2 pieces").
- **`fetch <oid> <name>`:**
  - wait until those records are applied (progress on stderr, timeout `zrdt.fetchTimeout`);
  - run `git fetch --update-shallow <mirror> refs/zrdt/r/…:refs/zrdt/tmp/…` into the user's
    repository, then delete the temporary refs;
  - answer with a blank line. git runs its own connectivity check.

  The fallback, if a nested fetch misbehaves inside a helper (G4 spike): `pack-objects` from the
  mirror, `index-pack` into the user's repository, and append to its `shallow` file. That works on
  2.43 (fact check B) but is undocumented.
- **`option depth`, `deepen-since`, `deepen-not`, `unshallow`:** "history before <commit> was not
  shared with you".
- **Not offered:** `connect`, `stateless-connect`, `import`, `export`. Signal has no live two-way
  channel, and fast-import would rewrite object ids.

### 2.8 Newcomers and sharing

- **Bob is added** to the Signal group. Per channel, JOIN §6 gives him a relative store: only the
  records that seat him, with `after` structure and boundary digests for the rest. He gets no older
  opening, table entry, pack or carrier.
- **His first clone** is empty, with the notice: "this repository has history you were not given;
  ask a member to run git zrdt share-base".
- **The gate fires for him.** Every later push that builds on history he lacks is refused until a
  member shares something deliberately. The fork helps:
  - at the Signal group update that adds him, each member active in the repository sees "Bob has
    no history of repo X. Share main with him?";
  - the helper's error names both ways out.
- **Three share commands.** Each runs only from a user action and sets the share flag. Each goes to
  the whole channel, never 1:1, so the gate can count it.
  - **`git zrdt share-base <rev> [--ref name]`:**
    - K = {S}, listed in shares if an earlier record carried S;
    - the pack holds S and its tree, minus what every seat already has;
    - the updates re-assert the current values of the named refs, so Bob learns those names, on
      purpose;
    - older members skip the download.
  - **`-o zrdt.share-tree` on a push:** K is fresh. Seats that lack the parents get K's full trees
    as a cut. The merge case: Bob gets M, its tree and its blobs, never the feature commit F (D2,
    `git fsck` clean, `git cat-file -e F` fails).
  - **`git zrdt share-history <range>`:** carries the old commits themselves (as shares).
- **Shown to everyone.** Every member sees "Carol shared main@S (its files, message and author,
  not its history) with the channel". Optional per-group strict sharing, mirroring JOIN's strict
  mode: only an author of a record that carried S may share S.
- **What Bob learns:**
  - the content of records sent to him, and the trees of shared commits;
  - the parent ids of a shared commit. These are opaque, but unsalted (§3.2).

  Without a share, he learns nothing about older commits, trees, names or messages.
- **Re-add** (JOIN §6.5): records from his first interval still entitle him; the gap is cut.
  **Identity key changes:** a member whose key changed counts as a newcomer.

### 2.9 Retransmission, retention, availability

- **Missing records:** JOIN's per-digest `SERVE`.
- **Missing pieces** (a dead carrier, one that never came, or a bad piece): a TRANSPORT re-upload
  request (§5.4), under the via rule. The responder must hold r's exact pack bytes, obtained
  through r.
- **Pinned bytes cost nothing extra.** `index-pack --stdin` stores a non-thin pack byte for byte
  (checked, §0), so the mirror's pack file for r *is* r's blob. The mirror keeps every received pack
  with a `.keep` file and `gc.auto=0`. The user's own repository can run `gc` freely.
- **Kept for good:** records, openings and the git table. Freshness, the gate, refs and agreement
  all need them. A git channel offers no erase in v1; retire the whole channel instead (epochs,
  TRANSPORT §9).
- **After the CDN copy expires** (about 30 days), any member that holds r's pack re-uploads it.
- **Later (G7): repack.** This is D2's idea. Any member that applied r builds a fresh pack for a
  seated requester. It travels as a sealed `SERVE` carrier with an uncommitted root, gated like
  carriers (after a released `addressed` entry for r, and only if r was applied). The requester
  checks it with `CHECK_PACK` against r's committed body. Availability then needs anyone's
  repository, not the original bytes.
  - Why it stays inside R1: `checkPack_rooted` keeps a repack inside the trees of r's commits, and
    the gate made every seat of r entitled to r's parents.
  - What it needs: a transport change (`serve_repack`), which is why it comes later.

### 2.10 The helper and the fork

- **`git-remote-zrdt`** is TypeScript/Node, about 1.2k lines. It speaks the remote-helper protocol
  on stdin and stdout, and reaches the fork's per-app Unix socket with the `git` token (TRANSPORT
  §10). It holds no state of its own.
  - Every security check runs in `zrdtd`, called by the fork. So the helper need not be Lean (D1's
    reason for a Lean helper) and needs no C shim.
  - The `list` lines are Lean's output, so a member cannot inject protocol lines through a ref name.
- **Porcelain:**
  - `git zrdt status`: heads, compare code, divergent and shadowed refs, missing pieces, members
    who lack history;
  - `git zrdt log [ref]`: the refLog with forced flags;
  - `git zrdt who <commit>`: the record, its pusher and its provenance;
  - `git zrdt share-base | share-tree | share-history`.
- **The fork also:**
  - keeps the mirrors;
  - runs `CHECK_PACK` and `CHECK_PUSH` around `publish`;
  - applies records;
  - shows local notices ("Alice pushed main", "Bob has no history of repo X");
  - runs the add-time share prompt.

### 2.11 Wire, ops, sizes

`zrdtd` frame protocol 4, extending TRANSPORT §8:

| Op | Name | Request | Reply |
|---|---|---|---|
| `0x1D` | `GIT_BODY` | channel ‖ body | `OK`; `BAD_APP` (reason) |
| `0x1E` | `CHECK_PACK_BEGIN` | channel ‖ body ‖ BlobRef ‖ header + proof ‖ trailer + proof ‖ idx | session; `BAD_PACK` |
| `0x1F` | `CHECK_PACK_OBJ` | session ‖ kind ‖ content (chunked) | `OK`; `BAD_PACK` |
| `0x20` | `CHECK_PACK_END` | session | `OK`; `BAD_PACK` (reason) |
| `0x21` | `CHECK_PUSH` | channel ‖ field-201 bytes ‖ author ‖ links ‖ body ‖ mode | `OK`; `OLD_COMMIT`; `GATE`; `BAD_REF` |
| `0x22` | `GIT_REFS` | channel ‖ applied record digests | live values per name, shadowed flags, `list` lines |
| `0x23` | `GIT_HAS` | channel ‖ aci ‖ key (33) | entitled commits |

New statuses: `0x0E` `BAD_PACK`, `0x0F` `OLD_COMMIT`, `0x10` `GATE`, `0x11` `BAD_REF`.
`ACCEPT`, `ACCEPT_RECORD` and `ACCEPT_VIEW` on a git channel run `GIT_BODY` and fill the table.

**Sizes:**
- body: at most 32 KiB;
- K, per record: at most 512 commits;
- updates, per record: at most 64;
- the whole Content message: at most 64 KiB (TRANSPORT §5.1);
- the pack: one blob of any length, in pieces of at most 64 MiB, so the 100 MiB attachment cap does
  not bound repository size;
- eager download: up to 16 MiB per pack.

## 3. How R1, R2 and R3 hold

### 3.1 R1: no older data for later joiners, unless an author deliberately shares

| Attack | What stops it | Evidence |
|---|---|---|
| A merge of a pre-join branch, packed as a range, ships old commits, messages and blobs | `--no-walk` lists (host); in Lean, `checkPush_fresh` (an old commit leaves only as a declared share) and `checkPack_commits` (pack commits = K) | D1 `r1_exclusion.sh`: the leaky bundle carries 3 commits, and Bob reads blob "EXP-ONLY-v1 pre-join". D2 `exp1.sh`: `^C4 M` ships F |
| A bundle header names older commits' subjects | No bundle on the wire. The body holds no text except ref names | D1 log `-430d2fa3… e2`; D2 v3 bundle |
| New trees name older files; the first push after a join hands out the current tree | `checkPush_gate`, over *every* seated account. The share flag is committed and shown to all | D2 scratch `#guard`s: the merge fails the gate and passes with the share flag |
| A delete or update reveals the name of a branch a newcomer never saw | name rule (`checkPush_refs`) | new here |
| A ref pointed at an old commit | target rule (`checkPush_refs`) | D2 |
| A pack smuggles objects outside its commits' trees | `checkPack_rooted`, `checkPack_exact` (count, ids, header and trailer bound to the root) | D2 scratch: a non-rooted old blob fails |
| Content-addressed pull: a newcomer names an old commit in his own record, or asks for its pieces | His pack cannot contain the object, so `CHECK_PACK` fails at every receiver. The via rule; repack only for applied records | TRANSPORT §4.4 |
| Asking for more depth | `depth`, `deepen-*` and `unshallow` are refused | — |
| Channel catch-up or per-digest repair | JOIN `SERVE`: `serve_content`, plus `serve_blobs` for carriers | JOIN §7.1 |
| CDN pointer as a bearer token; Desktop's 3-day upload reuse | Carriers are content; fresh keys | TRANSPORT §4.3–§4.4 |
| A key swap | The gate compares key tags; the seal | JOIN §4.3 |
| The server lies to a pusher about membership | The fake member is seated, as in JOIN (Signal itself would deliver to him live). The gate fires and names the unexpected account | JOIN §8.1 |
| A modified pusher skips the checks | Every member audits over the causal past and gets the pusher's own answer (`checkPush_objective`). The pusher is named | §2.4 |
| The pusher lacks some openings | Entitlement is under-counted, so it gives a spurious `GATE` (friction), never a leak. A re-carry hidden that way is caught by the audit | — |

### 3.2 Residuals, accepted and stated

- **Ids of a shared commit's parents.** Git ids are unsalted, so anyone can test a guess (for
  example "based on upstream commit X"). They are weaker than zrdt's salted boundary digests.
- **Old content committed again** (a revert, cherry-pick or rebase) counts as new content. It is
  a deliberate paste, JOIN's non-goal. A later helper warning can flag it using patch-id.
- **Objects a member holds from outside the channel** (for example a GitHub clone) are fresh to
  the channel, and he may publish them.
- **On `git` (SHA-1) channels** the object checks hold unless a *member* produces a SHA-1
  collision. The server cannot inject objects, and git's SHA-1DC rejects known collision attacks.
  A member who wants to leak can paste anyway.

### 3.3 R2: designated-verifier authenticity only

- **Nothing new signs or MACs.** The body, ids, pack, idx and BEP 52 root are unkeyed hashes.
- **Signatures are refused.** `checkPack_unsigned` refuses `gpgsig`, `gpgsig-sha256`, `mergetag`
  and tag objects. Push certificates are `unsupported`.
  - The attack this stops: a member with `commit.gpgsign=true` pushes, and every member's mirror
    then holds a transferable signature over his work, which can be used against him. Without the
    Lean check this happens silently.
- **Authorship** is the record's author, through Signal's deniable channels: `live`, or
  `relayed(by)` until the author confirms (A8, `classify_spec`). Commit author and committer lines
  are shown as claims.
- **Residuals.** Compare codes and commit ids pin content, not authorship (JOIN §7.4). Signal's
  upload logs plus a member's device tie uploads to accounts; re-uploads add more such events
  (TRANSPORT §12).

### 3.4 R3: reuse first

- **From git:** the remote-helper protocol (`fetch`, `push`, `option`, `push-option`), the pack and
  idx formats, `index-pack`, `pack-objects`, `rev-list`, `shallow` with `--update-shallow`, the
  connectivity check, check-ref-format, object ids.
- **From Signal, through the transport:** sender keys, the CDN, pairwise sessions, retry, Signal
  groups as audiences.
- **Added, each for a gap:**
  - the body and table: git cannot tell a newcomer from a full member;
  - `CHECK_PACK` and `CHECK_PUSH`: git's range and bundle machinery ships older commits;
  - the register: there is no central ref server, yet concurrent pushes must converge;
  - share records: a bundle cannot express a shallow cut;
  - the signature guard: git signatures are transferable;
  - (later) repack: CDN copies expire, and the via rule needs the original bytes.

### 3.5 The server adversary

- **The server can:**
  - withhold or delay pushes. The gap shows, and the newest push can stay hidden until a later
    record or a compare code (`withheld_tail_undetectable`);
  - expire CDN copies early (members re-upload);
  - withhold a force push from some members (both values stay live and visible);
  - see sizes, timing, uploaders and download IPs;
  - lie to an author about membership (§3.1).
- **It cannot:**
  - inject a push (Signal authenticates the sender, and the record digest binds the body);
  - alter bytes undetected (the BEP 52 root, then `gitOid` recomputation);
  - read content;
  - make an honest member's `zrdtd` send older commits (`fresh`, `gate`, `serve_content`).
- **Members are honest or attributable.** A bad pack is refused and named. A push past the gate,
  an unflagged force, or a re-carry is named by the audit. Shares are visible to all. Closed groups
  only.

## 4. Theorems

Two kinds, as in JOIN §7. **Running-code theorems** are about functions `zrdtd` runs; they are the
ones that stop a leak caused by a host bug. **Spec theorems** state what a store means.

### 4.1 Carried over unchanged

Git records are ordinary app records, so everything TRANSPORT §7.1 carries over still holds:
- the 14 theorems advertised in `Api.lean` on `join` (the 11 plus JOIN's `agree_rel`,
  `serve_content` and `serve_content_complete`);
- the spec theorems in `Integrity.lean`, `Chat.lean` and `Rel.lean`;
- the running-code theorems in `Commit.lean`, `Serve.lean`, `Proto.lean` and `RelStore.lean`.

### 4.2 Transport theorems this app relies on (to prove there)

- `opening_bound`, `appOpening_lasting`, `run_accept_app`;
- `blobRoot_bound`, `checkPiece_sound`, `assemble_root`;
- `serve_blobs`.

### 4.3 New running-code theorems (`core/Zrdt/Git/{Obj,Body,Table,Check,Refs}.lean`)

| Theorem | Statement | Status |
|---|---|---|
| `gitOid_bound` | `gitOid k c = gitOid k' c'` → `(k,c) = (k',c')`, or a SHA-256 collision (SHA-1 on `git` channels). The header `kind SP decimal NUL` is prefix-free | to prove; needs injectivity of decimal lengths |
| `gitBody_canonical` | decode ∘ encode = id; encode is injective on valid bodies. With `opening_bound`, the record binds K, shares, prereqs, updates and the flag | to prove |
| `validRefName_safe`, `listLine_parse` | every parsed name passes `validRefName` and has no byte ≤ 0x20 or 0x7f; each line `GIT_REFS` renders parses back to exactly its (oid, name) | to prove (from D1) |
| `run_accept_git`, `table_encode_reopens` | the accept ops add a table entry only from a matching opening whose body passes `GIT_BODY`, and the entry is that body; otherwise `BAD_APP` and nothing changes. The table survives save and reopen | to prove |
| `checkPack_exact` | on `OK`: the idx checksum is the committed trailer, the count is the committed header's, and the i-th idx id = `gitOid` of the i-th object streamed | to prove |
| `checkPack_commits` | on `OK`: the pack's commit ids are exactly K, and prereqs = parents(K) \ K | to prove |
| `checkPack_rooted` | on `OK`: every non-commit object is reachable from a K commit's root tree through pack trees | blob half proved in scratch (`checkPack_blob_rooted`) |
| `checkPack_unsigned` | on `OK`: no commit carries `gpgsig`, `gpgsig-sha256` or `mergetag`, and there is no tag object | proved in scratch, without the tag case |
| `checkPush_fresh` | on `OK`: every c ∈ K \ shares is in no K of the causal past | proved in scratch, on simplified types |
| `checkPush_gate` | on `OK` without the share flag: every seat with a non-zero tag that is not the author is entitled, under the same tag, to every prereq | proved in scratch, on simplified types |
| `checkPush_refs` | on `OK`: the target rule and the name rule hold for every update | to prove |
| `checkPush_objective` | `CHECK_PUSH`'s answer depends only on the record (body, audience, author, links) and the table restricted to its causal past | to prove; a congruence lemma |
| `refView_spec` | (d, v) is live for n iff a stored record d with a matching opening assigns n := v, and no stored record with a known body that assigns n strictly reaches d | to prove; D1's scratch proves `live_sub_log` and passes 11 `#guard`s, including all 120 orders of five records |
| `refState_congr`, `refLog_mono`, `force_visible`, `shadowed_spec` | the view depends only on the records and openings; accept and merge never remove a refLog entry; `shadowed` means exactly what §2.5 says | to prove (from D1) |
| `run_checkPack`, `run_checkPush` | the frame ops compute the functions above, and leave the store unchanged | to prove |

### 4.4 New spec theorems (`Crdt/Merkle/GitApi.lean`)

- **`refs_agree`** (advertise): two closed channel stores with equal heads, each holding a
  matching opening for every record, have equal ref views, or SHA-256 has a collision. Proof:
  `CheckedStore.agree`, then `opening_bound`, then `refState_congr`.
- **`refs_agree_rel`:** a newcomer's ref view equals the view over the responder's served view,
  with openings restricted to the records that seat him, or a collision (`newcomer_agree'` plus
  `refState_congr`).
- **`cuts_are_shares`** (advertise; the R1 statement for git): in a store whose records all pass
  `CHECK_PUSH` over their causal past, take any account s other than r's author, entitled to a
  commit c through record r. Then every parent of c is entitled to s, or r has the share flag.
  So every cut in s's history is a committed share, visible to the whole channel. Proof: lift
  `checkPush_gate` per record. With `checkPack_rooted`, this means everything s can read lies in
  trees he is entitled to, or in a share.

### 4.5 To advertise in `Api.lean`

- `checkPush_fresh`, `checkPush_gate`, `cuts_are_shares` (R1 for git);
- `checkPack_rooted` (R1);
- `checkPack_unsigned` (R2);
- `refs_agree` (convergence).

Each gets a satisfiable example and a rejected bad output (the scratch `#guard`s, ported). The
Comparator challenge is updated with them. Comparator runs only as the very last step, with
kejace's approval.

### 4.6 Tests (`#guard`, named examples, end-to-end on the mock)

- **Regressions, ported from the scratch scripts into the repository:**
  - D1 `r1_exclusion.sh`: the leaky range bundle;
  - D2 `exp1.sh`: the range merge and the shallow merge;
  - the bundle-subject case: there is no bundle path, and the test asserts it.
- **Lean `#guard`s:**
  - the merge with parent F fails the gate, and passes with the share flag;
  - a pack carrying F fails freshness unless F is a share;
  - a changed key tag fails the gate;
  - a non-rooted old blob fails `CHECK_PACK`, and so do a spurious prereq, a signed commit and a
    tag object;
  - a delete of a branch Bob never saw fails the name rule;
  - a ref name with LF, a space, `..` or `.zrdt-` fails;
  - a SHA-1 oid on a `git-sha256` channel fails;
  - the audit at a receiver gives the pusher's own answer;
  - the register gives the same live set under all record orders.
- **End-to-end on the mock:**
  - concurrent pushes, then their merge;
  - a force push and its audit;
  - a newcomer: an empty clone, then `share-base`, a shallow clone, and his push applying at an old
    member;
  - CDN deletion, then re-upload;
  - a bad pack named;
  - a signed commit refused;
  - a chain of 1,500 commits;
  - git 2.39 to current.

### 4.7 Trusted base and host duties

- **Trusted:**
  - `git index-pack` lists every object of the pack in the idx. Lean binds the idx to the committed
    bytes (checksum, count) and recomputes every id;
  - the fork's streaming of idx entries into `CHECK_PACK` (Lean catches an omission);
  - git's ancestry checks for the forced-flag audit and for presentation;
  - `pack-objects` and `rev-list` for planning (efficiency only).
- **Host duties:**
  - shares only from a user action;
  - the applied(r) fact;
  - cuts only for share records;
  - refuse deepen requests;
  - the nested fetch with `--update-shallow`;
  - the mirror's `.keep` files.

## 5. Limits, and what is honest to claim

**Honest to claim:**
- **Serverless sharing:** members of a Signal group push and fetch a git repository with no git
  server. Content is end-to-end encrypted, and the server sees blobs, sizes and timing.
- **Checked pushes:** a pack that does not match its committed header, or that carries a
  signature, is refused at every member and named.
- **Convergence:** members with equal heads see the same refs (`refs_agree`).
- **No older history for newcomers:** a member added later gets no older commit, tree, file name,
  message or branch name unless a member deliberately shares, and every share is committed and
  shown to everyone. This is checked by proved code in `zrdtd` (`checkPush_gate`,
  `checkPush_fresh`, `checkPack_rooted`, `cuts_are_shares`), not left to the helper's care. The
  residuals are in §3.2.
- **No signatures anywhere;** authorship is deniable.
- **TCP-like** in reliability, retransmission, integrity and completeness, as the transport is.

**Not to claim:**
- **It is not a git server.** `ok` means published, not won. There is no central ref order, no
  pre-receive hook, no pull requests, and no atomic transactions across members. Concurrent pushes
  show as extra `…zrdt-…` branches until someone merges.
- **No ordered stream, flow control or latency bound.** It is store-and-forward; the server can
  delay pushes and hide the newest one for a while.
- **No metadata privacy from the server:** sizes, timing, uploaders and download IPs are visible.
- **Not for large or busy repositories.** `CHECK_PACK` hashes decompressed objects in Lean at about
  45 MiB/s, so 1 GiB takes about 25 s per member. Very large histories also make the table large
  (32 B per commit).
- **Not on Signal's official servers, beyond small pushes a person starts** (terms of service and
  rate limits). Run it on the mock or a self-hosted server.
- **Newcomers stay shallow.** `log`, `blame` and `bisect` stop at cuts. Each pre-join line that
  continues needs one share.
- **Friction:**
  - every add to the Signal group, and every identity-key change, blocks pushes until someone
    shares;
  - signed commits are refused;
  - v1 has lightweight tags only;
  - SHA-256 only until stage G6.
- **Not supported:** LFS, partial clone, submodule recursion, push certificates, SHA-1↔SHA-256
  conversion, or a smaller audience inside one channel.
- **Stock clients take no part.** Availability after about 30 days rests on members that keep the
  packs.
- **Lean never runs git.** Ancestry (the forced audit and presentation) and pack planning are host
  code.

## 6. Effort and build plan

Prerequisites: JOIN stages 1–3 (stage 1's core is on `join`; the fork's stages 2 and 3 are not
started), and TRANSPORT stages 1–4.

| Stage | Content | Agent-days | Needs |
|---|---|---|---|
| G1 | **Lean core, `git-sha256`.** `Git/Obj` (`gitOid`, commit, tree and idx parsers); `Git/Body`; the table in `zrdtS4`; `CHECK_PACK` with header and trailer proofs; `CHECK_PUSH` (fresh, gate, refs, causal past); `GIT_REFS` with rendered lines; `GIT_HAS`; the §4.3 theorems; vectors from real SHA-256 repositories | 7 | TRANSPORT 1 |
| G2 | **Spec and Api.** `refs_agree`, `refs_agree_rel`, `cuts_are_shares`; `Api.lean` entries with examples | 2 | G1; JOIN 3 (relative restatements) |
| G3 | **Fork.** Mirror per channel; the apply pipeline (prereqs, cuts, quarantine, streaming, `.keep`); checks around `publish`; audit warnings; notices; the add-time share prompt; eager-download policy | 4 | G1; TRANSPORT 3 |
| G4 | **Helper** (TypeScript) and porcelain. Spike first: a nested `fetch --update-shallow` inside a helper, with the fallback | 4.5 | G3 |
| G5 | **End-to-end** on the mock (TRANSPORT 4's CDN deletion and 413/429 injection); the ported regression scripts; the git version matrix | 3 | G4 |
| G6 | **`git` (SHA-1) channels.** Lean SHA-1 with NIST and git vectors; SHA-1 idx; theorems restated "or a SHA-1 collision" | 2 | G1 (parallel with G3) |
| G7 | **Later.** Repack with `serve_repack` (2); unsigned annotated tags (1); a Lean ancestry table for the forced audit (1) | 4 | G5; a transport change |

- **Total, G1–G6:** about 22.5 agent-days (4.5 weeks), on top of JOIN and TRANSPORT.
- **Critical path:** JOIN stage 3 and TRANSPORT stage 3 (the fork, about 2 weeks), then G3, G4, G5.
- **Parallel work:** G1 starts once TRANSPORT stage 1 (`App.lean`, `Blob.lean`) exists, and runs
  alongside TRANSPORT 2–3 and the torrent app. G6 runs alongside G3.
- **Riskiest items:**
  - `gitOid_bound`: decimal injectivity without Mathlib;
  - `refs_agree_rel`: it rests on JOIN's pending relative restatements;
  - the G4 spike: helper-time shallow handling across git versions.
- **Comparator** runs only as the very last step, with approval. Never run Comparator, `lake check`
  or `leanchecker` before that.

## 7. Design history

- **TRANSPORT's baseline (§12): the bundle as an opaque blob, with R1 for git left to the app.**
  Rejected. Both designers showed, on git 2.43, that this baseline leaks:
  - the range on a merge ships the old branch;
  - bundle headers carry older commits' subjects.
- **D1, `git-remote-zrdt` (score 6.5).**
  - *What it proposed:*
    - one record per push, with a body (updates, prerequisites, the new commit list) and the bundle
      as blob 0;
    - bundles built with `--not` every published tip;
    - Lean freshness over commit lists that git reports;
    - `checkBundle` comparing those lists with the body;
    - a transport op `COVERS` at freeze, requiring every *participant* (an author in the channel)
      to be seated, under the same key, in a source of each prerequisite;
    - snapshot records for newcomers, written straight into `.git/shallow`;
    - a Lean helper binary.
  - *Why it was not the base:*
    - **R1 rests on host-read object lists.** Lean never sees an object; a bug in reading
      `rev-list` or `show-index` output makes a leaky bundle look fresh.
    - **Seated non-participants still receive the bundle.** Carriers go to the whole group, and the
      fork pre-fetched up to 64 MiB. So they get new trees naming older files, older commit ids,
      and the bundle header's subject lines. D1 accepted only "prerequisite commit ids" as a
      residual.
    - **Its own log shows the subject leak** (`-430d2fa3… e2`).
    - **Engineering costs:** a C shim (Lean v4.35 has no Unix-socket client) and undocumented
      `.git/shallow` writes.
    - **The advertised ref value depended on the viewer.**
  - *Kept:*
    - SHA-1 channels through two app tags;
    - the causal multi-value register and its scratch proof;
    - the forced flag, the forced-flag audit, `refLog_mono` and `force_visible`;
    - `validRefName_safe` and `listLine_parse`;
    - receiver-side freshness audits;
    - `shadowed`;
    - dropping a value that is an ancestor of another live value;
    - the "Bob has no history" notice;
    - a key change counting as a newcomer;
    - the deepen refusals;
    - the HEAD symref;
    - its experiment, as a regression test.
- **D2, `zgit` (score 7.5): the base. Changed:**
  - SHA-256 only → SHA-1 channels as stage G6;
  - an explicit `supersedes` list in each update → D1's causal register (no extra field, and
    proved order-free);
  - `checkPush_refs` gains the name rule;
  - `CHECK_PUSH` runs over the causal past and at every receiver, not only at the pusher;
  - cuts come only from share records, instead of "a prereq no held record carries, with a
    complete causal past";
  - share-base sets the share flag explicitly (otherwise its own gate would refuse it);
  - pack header and trailer are bound to the committed root by Merkle proofs;
  - the pinned bytes are the mirror's own packs (checked byte-identical);
  - repack moved to a later stage;
  - `cuts_are_shares` and `checkPush_objective` added.
- **Considered and dropped:**
  - **D1's participants-only gate,** to spare non-users a share prompt: it leaks names and ids to
    seated non-participants (above).
  - **Sending carriers only to entitled members:** a seated member is entitled to a record's content
    under `SERVE`, so the rule would contradict TRANSPORT's carrier rule.
  - **A list blob for long commit lists:** the table would then depend on a download; chains keep it
    a function of openings.
  - **`stateless-connect` or `connect`:** Signal has no live channel, and `stateless-connect` is
    fetch-only and labelled internal.
  - **`import` and `export`:** fast-import rewrites ids.

## 8. Review brief

The reviewer should try to break the design, then harden it.

### 8.1 What to try

1. **R1.** Get an older object, file name, message, branch name or commit id to a newcomer beyond
   §3.2. Angles to try:
   - chains;
   - a share flag on one chain record;
   - concurrent pushes during an add;
   - a pusher whose relative store links only some heads;
   - the name rule with re-created names;
   - presentation refs;
   - the mirror's shallow file after a later share;
   - repack (G7);
   - prereqs on a SHA-1 channel.
2. **The gate's objectivity.** Check that `CHECK_PUSH` over the causal past really is reproducible
   at every member, including members that hold some of those records structure-only.
3. **The trust boundary.** Can a buggy fork make `CHECK_PACK` pass a pack whose objects git
   imports differently? Look at idx order, the count, header and trailer proofs, and objects split
   across `OBJ` chunks.
4. **R2.** Find a transferable artefact: signatures in unusual commit headers, tag-like content in
   commit messages, compare codes, upload logs.
5. **Convergence.** Check `refs_agree`'s hypotheses (same openings), and whether presentation can
   differ between members in a way that matters.
6. **The facts.**
   - `--update-shallow` inside a helper, and helper-written `shallow`, on git 2.39 to current;
   - `index-pack` byte identity for non-thin packs across versions;
   - the claim about SHA-1DC.
7. **The effort figures,** against the size of `Serve.lean` and `Proto.lean` today.

### 8.2 Known weak or unproven points

1. Every theorem in §4.3–§4.4 is unproved except four scratch lemmas, two of them on simplified
   types.
2. `refs_agree_rel` depends on JOIN's relative restatements (JOIN §12.3.5), which are not started.
3. The gate costs a share prompt after every add and every key change. Users may answer it with
   `-o zrdt.share-tree` by habit, which weakens R1 in practice.
4. `CHECK_PACK` hashes in pure Lean (about 45 MiB/s). Moving hashing to the host would enlarge the
   trusted base.
5. Repack needs a transport change that TRANSPORT.md does not have. Until G7, availability after
   CDN expiry rests on members that keep the packs.
6. Inherited from the transport:
   - unknown production rate limits and a private spam filter;
   - the terms of service;
   - the mock server holds attachments in RAM;
   - stock iOS's handling of Content 205 is unverified.

### 8.3 Open questions for kejace

1. **SHA-1 channels** (stage G6): include them, so existing repositories and hosts work, at the cost
   of statements that read "or a SHA-1 collision" (practical for a member)? Recommended: yes, after
   G1.
2. **Signed commits:** refuse in Lean with no override (as planned), or allow a per-push override
   with a warning (D1)? Recommended: no override in v1.
3. **The gate's friction:** accept "every add blocks pushes until a share", with the add-time
   prompt? Or allow D1's participants-only relaxation, which leaks file names and ids to seated
   non-users? Recommended: accept the friction.
4. **Strict sharing** (only an author who carried a commit may share it): build it, off by default,
   like JOIN's strict mode?
5. **Repack and annotated tags:** later (G7), as planned?

## Open issues from the adversarial review (not yet folded in)

Two breakers attacked this plan after it was written: breaker 1 as the malicious server and
network, breaker 2 on R1, R2 and the git semantics. The revise step that would have folded their
findings into §0–§8 did not run, so **the sections above still contain the claims these findings
contradict.** Breaker 2 asked that the design be scored again once the fixes are in; the 7.5 in §0
predates these findings. Both breakers worked against join `acbd70a` (protocol 3) and ran no
Comparator, `lake check` or leanchecker.

Evidence: scratch files under `/tmp` (not in any branch, may be gone after a reboot). Signal
source files are named as the breakers cited them, in Signal-Desktop v8.33.0 (a read-only copy is
at `/tmp/zrdt-spike-fork/sd-v8.33.0`). "Plan reading" means the breaker argued from this document
and the shipped Lean, without a test. Attack numbers count from 1 in each breaker's report.

### Fatal

**G-F1. An empty causal past sends the whole older history to newcomers, and nobody is named.**
(Breaker 2.) Freshness, the gate and the name rule are evaluated only over the records the new
record links. A push with root commits and no links passes them vacuously, and every auditor
agrees (`checkPush_objective`). Triggers: (a) honest: a member whose key changed keeps his old
clone; his relative store has only boundary heads, so `linkable` returns nothing, `GIT_REFS` lists
no refs, and `git push team main` sends the entire history with no share flag; (b) honest: the
plan's own epoch advice (§2.9, `repo#2`) or a second repo name in the same group starts from an
empty table; (c) a modified client that drops links. Two rows of §3.1 are then false.
- Fix: (1) a **root rule** in `CHECK_PUSH`, publish mode, over the pusher's whole store: a commit
  with no parents, or any push with an empty causal past, needs the share flag unless the channel
  store is otherwise empty; (2) a second audit at receivers over the auditor's whole table that
  names any re-carried commit not covered by a share (not objective, but names only true
  re-carries); (3) **one git table per (Signal group, object format)**, shared by every repo
  channel and epoch; an epoch's first record imports its predecessor's table through committed
  heads; (4) the helper refuses, on a relative store, a push to a remote that lists no refs unless
  `-o zrdt.share` is given.
- Evidence: plan reading plus `core/Zrdt/RelStore.lean:738` (`linkable` on a relative store).

### Major

**G-M1. The share escape hatch turns a TOFU key swap, or a removal the server hides, into
disclosure of the whole current tree.** (Breaker 1, attack 1; breaker 2's minor "the add prompt
makes a server lie about membership worse" is the same mechanism.) §2.8 counts a member whose key
changed as a newcomer, every push then fails with GATE, and the §2.6 error text tells the pusher to
run `share-base` / `-o zrdt.share-tree`. The share goes to the frozen audience, which seats the
server's key. A hidden removal works the same way. Stock Signal would give the server only new
messages. Breaks JOIN §1 ("inherits TOFU, must not amplify it").
- Fix: the GATE reply gives a reason per (account, tag): `NEW` (no causal-past record seats it),
  `KEY_CHANGED` (seated only under another non-zero tag), `NOT_COUNTED` (a causal-past record by
  another author leaves it out of field 201). Only `NEW` gets the share hint. Share commands refuse
  `KEY_CHANGED` seats until the new key is verified or explicitly approved, and refuse
  `NOT_COUNTED` seats. The confirmation lists exactly the accounts the share newly entitles, and
  freeze aborts if that set changed. Never prompt to share on a key change; show the add-time prompt
  only for an add seen in a member's end-to-end group update, with the safety-number status, and
  say that a share sends all current files.
- Evidence: `SignalProtocolStore.preload.ts:2013-2020, 2205-2212` (Desktop trusts a new key for
  sending after 5 s unless verified); plan §2.6, §2.8, §3.1.

**G-M2. Freeze race: an honest push silently overwrites a concurrent one, and the honest pusher is
blamed.** (Breaker 1, attack 2.) The helper's fast-forward check runs before the piece uploads;
links are taken only at freeze. The server, which sees the upload size in advance, delivers Carol's
concurrent push in that window; Alice's record then links it and supersedes it with forced = 0,
Carol's commits leave `main`, and every forced-flag audit names Alice. Deletes behave the same.
- Fix: restore D2's **explicit, committed supersedes list** per update; `CHECK_PUSH` checks each
  listed record is in the causal past, assigns the name, and seats the author under his tag;
  `live(n)` = assignments no known record lists; the helper lists exactly the values it checked,
  and the forced-flag audit compares only against those. Host-only stopgap: freeze with the links
  captured when the helper ran its check.
- Evidence: `/tmp/zrdt-apps-gitbreaker1/RaceMvr.lean` (`lake env lean`, v4.35.0, no imports, no
  `sorry`, every `#guard` passes): live = `[(3,12),(2,11)]` at plan time, `[(2,11)]` at freeze;
  `WebAPI.preload.ts:4342` (`uploadSize` sent with the upload form).

**G-M3. A newcomer takes over a branch he never saw; the displayed value can be gamed.** (Breaker
1, attack 4; breaker 2, attack 3.) Bob's relative store holds older assignments of `main` only as
boundary digests, so `GIT_REFS` shows no `main`, his push needs no force, and at every old member
his record reaches and supersedes the team's `main` (the forced-flag audit then blames him). If his
links are empty, his value is concurrent, and §2.5 picks the displayed `main` by smallest record
digest: a coin flip that moves old members' `team/main` without a forced-flag warning, and a member
can grind record nonces (two SHA-256 per try) to win it.
- Fix: the supersedes list of G-M2 (Bob can only list records that seat him), or the rule "an
  assignment supersedes a value only if that value's record seats the assigning author under his
  tag" (objective, from committed audiences). While values diverge, give none of them the plain
  name: list each as `n.zrdt-<hex>` until someone merges. The helper warns a member holding
  boundary digests before he creates a name.
- Evidence: `/tmp/zrdt-apps-gitbreaker1/RaceMvr.lean` (live = `[(6,99)]`); plan §2.5.

**G-M4. Framing by withholding content.** (Breaker 1, attack 3.) The audit (§2.7 step 6) and
prerequisite repair (§2.7 step 1: "If the gap cannot be closed, r's author pushed past the gate;
report it") read a table that holds only records with openings. The server drops a record q's live
copy to Mike, drops his requests to members holding q's content, and routes one to a member who
holds q structure-only (made to look unregistered at q's enqueue, so it had a zero tag); `SERVE`
returns q as `after`. Carol's later honest push r, which builds on q, then fails Mike's audit and
names Carol. `checkPush_objective` holds only for members that hold every opening in the causal
past; newcomers never do.
- Fix: audit mode returns `OK`, `VIOLATION` or `UNKNOWN` (with the causal-past records held
  without an opening); `VIOLATION` only when every opening in r's causal past is held; warn only on
  `VIOLATION`; restate `checkPush_objective` with that hypothesis. In §2.7 step 1 an unresolvable
  prerequisite is a gap ("content not available from <responder>", JOIN §4.4), never the pusher's
  fault.
- Evidence: `/tmp/zrdt-apps-gitbreaker1/RaceMvr.lean` (the gate passes with openings {q, r} and
  fails with {r}); `core/Zrdt/Serve.lean` (`serve`: not entitled here and q in `up`).

**G-M5. The audit blames honest newcomers and its warnings tell them about older history.**
(Breaker 2, attack 4.) A pusher with a relative store cannot reproduce the audit. Bob merges a
public upstream commit U that Alice pushed before he joined: OK at Bob, `OLD_COMMIT` at auditors,
Bob is named, and the warning tells him U was carried before. Creating `refs/heads/release`, a
name used before he and another newcomer joined, gives `BAD_REF` the same way. This reopens the
existence check that TRANSPORT §4.4's via rule closes for blob roots.
- Fix: run the audit over the causal past restricted to records whose committed audience seats the
  author under his tag (what he could hold), so he can reproduce it. Show re-carries from records
  that do not seat him as information, not blame, and only to members seated in the original
  record. Never send audit results to the pusher's devices.
- Evidence: plan reading (§3.2 says objects from outside the channel are fresh).

**G-M6. Everyday git commands copy older content into fresh commits, and every proved check
passes.** (Breaker 2, attack 2.) `git merge --squash` of a pre-join branch writes each squashed
commit's id, author, date and message plus its files; `git revert <old>` writes the old subject and
id and restores the old blob byte for byte; rebase, `cherry-pick -x` and `git checkout <old> --
path` do similar. Freshness and the gate look only at commit ids; `checkPack_rooted` keeps objects
inside K's trees, which can hold anything; `cuts_are_shares` says nothing about file content.
§3.2 calls these a "deliberate paste" (and omits squash); §5's "no older commit, tree, file name,
message" is false.
- Fix: **freshness per object in Lean**: the table keeps, per git record, the ids of the objects
  its pack carried (32 B each); without the share flag, `CHECK_PUSH` refuses any pack object
  carried by a causal-past record that does not seat every current seat (exempt blobs under about
  64 B, such as empty files). Add a host warning (not a theorem) for commit messages naming
  table commit ids some seat is not entitled to, and a patch-id check. Restate §5 as "no older git
  object is sent", with edited copies of old content as the residual.
- Evidence: `/tmp/zrdt-apps-breaker2/exp1` (git 2.43; squash and revert confirmed).

**G-M7. The share flag is one bit for the whole record and switches off the name rule for every
update in it.** (Breaker 2, attack 5.) `git push --prune`, `--mirror` or `--all` with
`-o zrdt.share-tree` reveals every deleted or updated branch name while the notice says only
"Carol shared main@S". The HEAD symref update (op 2) carries a target `refs/heads/<x>` that
neither the name rule nor the target rule covers. Re-creating a common old name (`fix`, `wip`)
gets `BAD_REF`, which pushes users toward the flag.
- Fix: commit what a share covers: `shares` for commits plus a committed `sharedNames` list; exempt
  only the listed names; apply the name rule to symref targets; refuse deletes, and more than one
  ref update, in a share-tree record; the notice lists every name and commit the share reveals.
- Evidence: plan reading (§2.4, §2.6).

### Minor

**G-m1. Claims that depend on server delivery.** (Breaker 1, attack 5.) The server can deliver a
share record only to the newcomer; old members see it only when a later record links it
(`withheld_tail_undetectable`). "How many members it reached" (§2.6 step 6) would come from the
server's send result. Fix: reword as "shown to each member when it, or a later record that links
it, arrives"; `git zrdt status` lists shares not yet confirmed by a live record from each member
(`CheckedStore.confirmed`); derive "reached" from confirmations. Evidence: plan reading.

**G-m2. Metadata beyond what §1 claims.** (Breaker 1, attack 6.) Content 205 is padded only to
80-byte blocks, so the server learns the counts of commits, shares, prereqs and updates to within
about 2.5 oids, ref-name lengths and the number of carriers; a tiny body plus a large blob after an
add identifies a share-base and the snapshot size; the upload form reveals each push's size and
timing before it is sent. Fix: pad the body to fixed buckets (1, 4 or 32 KiB) with a committed
padding field; state the remaining shape leaks in §5. Evidence:
`OutgoingMessage.preload.ts:123-143`.

**G-m3. Rate-limit abuse and quota burn.** (Breaker 1, attack 7.) The server can delete each CDN
copy after one download, 404 re-uploads, drop sealed replies after the upload, or swap a key
between enqueue and freeze so `CHECK_PUSH` fails after every piece is uploaded. Each costs upload
quota (1 GB burst then 1 MB/s; 50 forms then 1 per 1.2 s) and can trigger a 428 challenge that
also blocks ordinary attachments; a network attacker can do the same through timeouts. Fix: a
re-upload budget per (record, requester, day); reuse one held carrier across requesters; re-run
`CHECK_PUSH` with current keys before each upload batch; re-upload only on CDN 404/403, and on a
timeout resume with Signal's own resume. Evidence: Signal-Server rate-limit defaults (fact check A).

**G-m4. The 24-hour sendLog path hands a recent pack to a swapped key.** (Breaker 1, attack 8.)
TRANSPORT §3.3 sends Content 205 with a send type that `shouldSaveProto` keeps. After a TOFU swap,
the server, as Mike, sends a `DecryptionErrorMessage` within 24 h, and Desktop re-sends the saved
proto, carriers included, to the server's key, bypassing `SERVE`'s key check and seal. Fix: give
Content 205 a fork send type that `shouldSaveProto` excludes; repair only through `SERVE`.
Evidence: `handleMessageSend.preload.ts:93-111`, `handleRetry.preload.ts:196-213`.
(The torrent breakers found the same; it is a TRANSPORT fix shared by both apps.)

**G-m5. The mirror's shallow file depends on arrival order.** (Breaker 1, attack 9.) §2.7 step 4
writes a cut only if a commit's parents are absent when its record is applied; the server can order
a share-tree record and a concurrent record carrying the missing parent differently per member, so
mirrors differ and a stale cut hides history the member holds, then `--update-shallow` copies it
into the user's repository. Fix: recompute `shallow` from the applied set after each apply (the K
commits of share records with an absent parent) and drop entries whose parents arrived. Evidence:
plan reading.

**G-m6. Chains are not all-or-nothing.** (Breaker 1, attack 10.) The server can fail a later chain
record's upload (413, 429, 428) or swap a key so its `CHECK_PUSH` fails at freeze, after earlier
records were sent, so commits from a push the user saw fail are published (refs stay atomic).
Contradicts "On GATE, OLD_COMMIT or BAD_REF nothing is sent". Fix: upload every piece of every
chain record first, run `CHECK_PUSH` on all of them, then freeze and send them back to back in one
queue job. Evidence: plan reading.

**G-m7. Notice wording the server can exploit; `refs_agree` overclaims.** (Breaker 1, attack 11;
breaker 2, attack 12.) "1 later record by Carol was not sent to you" is the phrasing JOIN §4.4
forbids (a structure-only copy may come from a responder holding another key, or from routing).
"Same heads give the same branches" also needs the same openings, and does not hold between a
newcomer and an old member: `refs_agree_rel` counts only records seating the newcomer, so a value
Carol assigned before the join can make old members see two values for `main` while the newcomer
sees one, with matching compare codes. Fix: "content of 1 later record not available from
<responder>"; `git zrdt status` shows, next to the compare code, how many records are held without
an opening and that the code does not cover refs he was not given; optionally a separate digest of
the ref view among members seated in the same records. Evidence: plan reading.

**G-m8. A newcomer can test whether a repo name exists.** (Breaker 2, attack 6.) He computes the
channel id for a guessed name and sends a catch-up; even seated in nothing, `serve` emits every
head as a boundary entry, so a reply shows the repo exists and how many heads it has. §2.8's "this
repository has history you were not given" depends on that; it contradicts TRANSPORT §2. Fix: on
channel stores `SERVE` returns an empty reply when `visList` is empty, and the host answers a
requester seated in no record of the channel identically (size and timing) whether or not it
exists; show the notice only after some record seats him. Evidence:
`core/Zrdt/Serve.lean:305-330` (`!linkedAny.contains d`).

**G-m9. The signature check is a deny-list.** (Breaker 2, attack 7.) `checkPack_unsigned` refuses
`gpgsig`, `gpgsig-sha256`, `mergetag` and tag objects and accepts anything else; `git fsck
--strict` accepts a commit with an unknown header `x-attest` holding an SSH signature block, and
`commit --amend` keeps it; tools add headers (jj's change-id); `refs/notes/*` can hold detached
signatures. Fix: allow only `tree`, `parent`, `author`, `committer`, `encoding` and refuse any
other header or continuation line; refuse `refs/notes/*` in v1 (or note blobs with armoured
signature markers). Evidence: `/tmp/zrdt-apps-breaker2/exp1` (git 2.43).

**G-m10. A member can forge a push in someone else's name.** (Breaker 2, attack 8.) Records carry
no signature; a member builds a record with author = Alice (or = newcomer Bob), links it from his
own live record and serves it as relayed. §2.5 and §2.7 apply it with no provenance condition,
notices read "Alice pushed main", and `CHECK_PUSH` exempts the author from the gate, so a record
forged as Bob carries older history to Bob and the audit blames Bob. Fix: grant the author's gate
exemption and show "pushed by" only for live or author-confirmed records; show values from
relayed records as `n.zrdt-<hex>` until confirmed; the audit treats the author of an unconfirmed
relayed record as an ordinary seat. Evidence: plan reading; JOIN A8 provenance rules.

**G-m11. Repack (G7) leaves the leak check to the responder's host.** (Breaker 2, attack 9.) A
repack's root is not committed and only the requester runs `CHECK_PACK`, after delivery. Fix: the
responder's `zrdtd` runs `CHECK_PACK` (rooted in r's K, plus G-M6's per-object check) before
`SERVE` emits the repack carrier; `serve_repack` requires that session's OK. Evidence: plan
reading.

**G-m12. Prerequisite repair has no commit-to-record lookup.** (Breaker 2, attack 10.) An
implementer who adds "which record carries commit X?" creates an oracle for whether the group ever
carried a public commit. Fix: specify that repair asks only for record digests from r's causal past
or boundary, and that no op or peer message takes a commit id from another member. Evidence: plan
reading.

**G-m13. On the pusher's side `CHECK_PACK` trusts the host's idx.** (Breaker 2, attack 11.) Lean
checks the idx's object count and a checksum field the host can copy; a host that builds or caches
the idx itself passes Lean while uploading a different object set, caught only after download.
Fix: `zrdtd` writes the pack itself (no deltas, zlib stored blocks, so no compressor in Lean) and
computes its root; or state that, on the pusher's side, R1 for objects rests on `index-pack` and
the host. Evidence: plan reading (§2.3).

### Attacks that failed (no change needed)

- CDN substitution, altered bytes, mixed byte ranges in a resumed download, carrier swaps: caught by
  Signal's MAC and digest (`AttachmentCrypto.node.ts:476`), then `CHECK_PIECE`, then
  `CHECK_PACK`. Keep blame for `CHECK_PIECE`/`CHECK_PACK` failures only, never for a Signal "Bad
  MAC". (Breaker 1.)
- Replay or reorder of records and replies: Signal drops duplicates, replies need an open request
  id, accept is idempotent, the register is a function of the record set (the judge's RefMvr checks
  all 120 orders). (Breaker 1.)
- Lying about membership or keys so that `zrdtd` sends older commits with no user action: the gate
  runs over frozen non-zero tags and re-uploads go through key-checked, sealed `SERVE` replies; the
  disclosure needs a user's share (G-M1). (Breaker 1.)
