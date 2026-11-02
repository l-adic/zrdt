# TORRENT_PLAN: sharing files in a Signal group over zrdt

Status: design, 2026-11-01. Not implemented. It builds on JOIN_PLAN v2 (branch `join`) and on
TRANSPORT.md (channels and the app message), and changes nothing in the demo build. It is the
judge's synthesis of two designs; §11 says what each proposed and why this one won.

> **Status (2026-11-01): design only, no code.** The adversarial review ran after this was
> written, but its findings are **not yet folded in**: they are listed, open, in the last section,
> "Open issues from the adversarial review" (5 major, 13 minor). Read that section before trusting
> any claim below.
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

**What this decides.** How members of a Signal group share a file or a folder so that:
- every member who fetches it ends with the bytes the author committed, or is told exactly which
  pieces are missing and gets them repaired;
- a member who joins later gets nothing older (not the bytes, the file names, or that the torrent
  exists) unless a member shares it again on purpose (R1);
- nothing is signed (R2), and Signal's own mechanisms do the transport (R3).

**What it builds on.**
- JOIN v2: the audience in field 201, `SERVE`, the seal, `ACCEPT_VIEW`, the relative store.
- TRANSPORT: channels (§2), the app message, Content 205 (§3), the app socket (§10), pacing and
  where to run (§11).
- It does **not** use TRANSPORT's blob layer: BlobRefs, carriers, the via rule, `SERVE`'s `have`
  and `carrier` entries, `GRANTS` (TRANSPORT §4, §5.3, the piece half of §5.4, ops `0x19`–`0x1C`).
  It uses **piece stores** instead (§3, §4). We recommend that TRANSPORT adopt piece stores as its
  only bulk mechanism. **This conflicts with GIT_PLAN.md** (written in parallel), which carries
  git packs as TRANSPORT blobs with carriers and the via rule. kejace decides (§13, question 1).

**The design in six lines.**
1. A torrent is one **announcement record A** in the group's `bt` channel, plus its own small,
   closed zrdt store, the **piece store**.
2. Each **piece** (4 to 64 MiB) is a record of the piece store. Its opening contains the piece
   bytes, so its commitment is a salted SHA-256 over them. A **manifest record F** links every
   piece and lists the files.
3. The author uploads each piece once to Signal's CDN. The list of pointers is itself an
   attachment, and its pointer sits inside A's committed body, so pointers go exactly where A's
   content goes.
4. Fetching means accepting F. `zrdtd` answers `MISSING` with the exact pieces still absent, and
   checks each downloaded piece by rebuilding its opening.
5. Repair is JOIN's per-digest `SERVE`, unchanged, run on the piece store. A member releases a
   piece only to an account that A's audience seats, sealed to the key it checked.
6. No signature, no new `SERVE` entry kind, and no host bookkeeping inside the R1 gate.

**Verdict.**

| Criterion (1 to 5) | Design 1 "zbt": BEP 52 blobs, carriers, via rule | Design 2 "bt/R": pieces as records |
|---|---|---|
| R1 against the server and a buggy host | 3: the gate on bytes is host state (`via`) | 5: bytes are openings; the shipped `serve_content` gates them |
| R2 | 5 | 5 |
| R3 | 4 | 4 |
| Provability | 2: Merkle induction, `SERVE` extended, 6+ proofs re-opened | 4: case splits and one composition; `SERVE` untouched |
| Engineering fit (zrdtd, fork, Signal) | 3: many new frames and tables | 3: bulk passes through `zrdtd` |
| User value | 4: per-file, lazy, BEP 52 identity, shared re-uploads | 3 (4 with the grafts) |
| **Total** | **21** | **24** |

**Base: design 2.** Grafted from design 1: the Lean-checked file table with safe paths, the trust
boundary (the app never sees pointers), the official and private profiles, pointer hygiene, the
repair scheduler's timeouts and blame, and `.torrent` export. Fixed in design 2: the repair reply
size, the index-to-digest binding, deterministic nonces, bytes-first field order, no layer
records, and `MERGE`/`SALVAGE` on piece stores (§11.3).

**Checked in this round** (scratch under `/tmp`, not in any branch):
- Design 2, on the shipped code (origin/join `acbd70a`): `/tmp/zrdt-apps-bt2/PieceCheck.lean`.
  Every `#guard` passes. C1: `ACCEPT_RECORD` of F before its pieces gives `MISSING` with exactly
  the absent piece digests. C2: a piece record whose opening holds 16 KiB is accepted, and a
  flipped byte gives `BAD_OPENING`. C3: after all pieces, heads are {F}. C4: unchanged per-digest
  `SERVE` gives a seated member the piece bytes, and gives a newcomer, or a seated member under a
  swapped key, only a bare boundary digest. C5: today's `ACCEPT_RECORD` also takes a piece record
  with no opening (a gap closed in §4.2). C6: a record with 4096 links is 131,161 B, over the
  server's 96 KiB cap.
- Judge's timing, compiled against the same code: `/tmp/zrdt-apps-btjudge/core/Bench/Main.lean`.
  A piece opening with its bytes **first** (the order chosen in §3.3) is accepted and served.

  | Piece | `COMMIT` | `ACCEPT_RECORD` | per-digest `SERVE` releasing it | peak memory |
  |---|---|---|---|---|
  | 4 MiB | 0.13 s | 0.09 s | 0.25 s | 84 MB |
  | 16 MiB | 0.31 s | 0.30 s | 0.90 s | 172 MB |
  | 64 MiB | 1.28 s | 1.30 s | 3.76 s | 610 MB |

  One hashing pass runs at about 50 MiB/s. `SERVE` hashes a held opening three times, as the
  code reads (`visList`, then `entitledHere`, then `serveOpening`). Peak memory is about ten
  times the piece size.
- Design 1's BEP 52 scratch, `/tmp/zrdt-apps-bt1`. Lean's pieces root equals the reference
  creator's root at six piece lengths. `climb_true` and `checkPiece_complete` are proved at spec
  level. It is kept for `.torrent` export (§6.7) and for later interop (§13, question 2).

**Read in this order:** JOIN §3–§6; TRANSPORT §2, §3, §10, §11; this document.

## 1. What the user gets

You share a folder with a Signal group the way you share a photo: `zbt add ~/trip --group Family`,
or a "Share files" button. Every member running the fork gets it from Signal's own CDN. Their
apps check every piece against what yours committed, and finish with byte-identical files. If
something is lost, they are told exactly which pieces are missing, and they get them from you or
from any member who kept them. After about 30 days, when the CDN copies expire, any member who
kept the files re-sends them, sealed, to whoever asks. Someone added to the group later sees none
of it, not even the names, unless a member shares it again on purpose. Nothing is signed: as in
Signal, nobody can prove to an outsider that you shared it.

What it is not: BitTorrent's network (no swarm, tracker or peer-to-peer link), fast (Signal's
upload limits set the pace), or for stock phones, which ignore it. On Signal's own servers it
suits small transfers that a person starts. Real use runs on the mock server or a self-hosted
one (TRANSPORT §11).

## 2. Shape

```
  bt channel (Signal group G, app "bt", name "files")      one per group; TRANSPORT §2
    ├─ A1  announcement: audience, name, ZrdtPieces{nonce, manifest = hash F1, L, k, N, pieceList}
    ├─ A2  ...
  piece store of A1 (id = SHA-256("zrdtT1" ‖ channel ‖ author ‖ nonce))     closed, never relative
    ├─ P0 … P(N-1)   one record per piece, no links; opening = nonce_i ‖ bytes ‖ index ‖ audience
    └─ F             links P0 … P(N-1); opening = nonce_F ‖ ordered piece digests ‖ file table ‖ audience
```

- **Why a separate store per torrent.** A lost piece stalls only that torrent. If F lived in the
  channel, every later record that linked it would wait. A torrent can be dropped as a whole. When
  it is complete, heads = {F}, which is the torrent's own compare code.
- **Who learns of a piece store.** Only holders of A's opening. The id derives from a secret nonce
  committed inside A. A newcomer sees older A's at most as opaque boundary digests (JOIN §6).
- **One audience.** Every record of a piece store carries A's audience, byte for byte. A's
  audience is the channel's: the Signal group's members at enqueue and freeze (JOIN §3.2). To
  share with fewer people, use a smaller Signal group (R3).
- **Records announce, frames transfer** (TRANSPORT §3.2). The channel holds only announcements.
  Pieces, requests and replies never enter the channel.

## 3. Formats

### 3.1 Layout

- **The stream.** The files concatenated in manifest order, with no padding. Its length L is at
  least 1 byte.
- **Pieces.** The piece length is 2^k with k from 22 to 26 (4 to 64 MiB): the smallest k with
  N = ⌈L / 2^k⌉ ≤ 4096. Only the last piece is short. So L is at most 256 GiB, and F links at most
  4096 pieces. There are no layer records (design 2 had them; §11.3).
- **Why at least 4 MiB:** the upload-form limit (50, then 1 per 1.2 s) binds below about 2 MiB,
  and per-piece overhead stays small. Many small files cost nothing extra: they share pieces.
- **Why at most 64 MiB:** Desktop compares the padded ciphertext with the 100 MiB default cap
  (largest plaintext 97.49 MiB), and `zrdtd` peaks at about ten times the piece size (§0).

### 3.2 The announcement A (Content 205, TRANSPORT §3.1)

Committed fields: 201 audience (JOIN), 210 `"bt"`, 211 channel name, 212 the bt body, 215 the
piece descriptor. A uses no field 213 (BlobRef) and carries no carriers.

```proto
message ZrdtPieces {                         // field 215, at most one; a transport field
  bytes  nonce = 1;                          // 32 random bytes: fixes the store id and every nonce
  bytes  manifest = 2;                       // the digest of F
  uint64 length = 3;                         // L ≥ 1
  uint32 pieceLog2 = 4;                      // k, 22 to 26, the smallest with N ≤ 4096
  uint32 pieces = 5;                         // N = ⌈L / 2^k⌉
  optional AttachmentPointer pieceList = 6;  // absent: on-demand (§6.5); opaque to Lean
}
message BtAnnounce { uint32 version = 1; string name = 2;      // field 212; for display only
                     uint32 fileCount = 3; string description = 4; }   // description ≤ 4 KiB
```

- **Lean `piecesOf o`** is strict. It requires exactly one field 215, in an opening that passes
  `appHeader` for `"bt"`. Inside it, fields 1 to 5 appear exactly once and 6 at most once, k is in
  range, N = ⌈L / 2^k⌉, and N ≤ 4096. Anything else is `BAD_REQUEST` at bind or open.
- **Field 215 is an addition to TRANSPORT's `appHeader`** (at most one, at most 1 KiB). It is
  app-neutral, so git can carry bundles in piece stores the same way.

### 3.3 A piece's opening

```
nonce_i ‖ [221 bytes] [220 index (varint)] [201 audience]          exactly these, in this order
nonce_i = SHA-256("zrdtN1" ‖ torrent nonce ‖ u32 i)                  computed by zrdtd
record  = (piece store id, commit, no links, A's author)
```

- `bytes` is 2^k long, or L − (N−1)·2^k for the last piece.
- **Built only by `zrdtd`,** from (index, bytes) and the store's descriptor (`PIECE_ACCEPT`,
  `PIECE_OPENING`). The host never builds or hashes an opening (A4).
- **Deterministic nonces.** The salt is the store id, which derives from the secret torrent nonce.
  So an opening is a function of (index, bytes, descriptor): a responder rebuilds it from the
  bytes alone, and the pointer list carries no nonces.
- **Bytes first.** The commitment hashes the fields in order, so everything except the audience
  can be hashed before the freeze. A later SHA-256 midstate op can then close the freeze window
  without a wire change (§5).

### 3.4 The manifest F

```
nonce_F ‖ [225 ordered piece digests: 32 × N bytes] [226 app manifest] [201 audience]
message BtManifest { string name = 1; repeated BtFile files = 2; }               // field 226 for "bt"
message BtFile { repeated string path = 1; uint64 length = 2; bool executable = 3; }
```

- **Links** are the N piece digests (sorted, as for every record). **Field 225** gives them in
  index order. Lean checks that the two hold the same N digests, with no repeats. So the index of
  every piece is bound by A's commitment, and repair can name exactly the pieces a selected file
  needs.
- **The file table** is checked in Lean (`btFiles`, grafted from design 1):
  - `name` and every path component pass `safeComponent`: 1 to 255 bytes of UTF-8; not `.` or
    `..`; no `/`, `\`, NUL, other control bytes or DEL; no leading or trailing space;
  - each path has 1 to 16 components and at most 1 KiB in total;
  - files are strictly sorted by path, compared component by component as bytes;
  - no path is a prefix of another, so a file is never also a directory;
  - at most 65,536 files and 16 MiB of manifest;
  - the lengths sum to L, so the files tile the stream. Offsets are implicit in the order.
- An empty file has length 0 and takes no bytes of the stream.

### 3.5 The piece list (a CDN object, not a record)

```proto
message ZrdtPieceList { bytes manifestRecord = 1; bytes manifestOpening = 2;
                        repeated AttachmentPointer pieces = 3; }        // N, in index order
```

- About 170 B per piece: 44 KiB for 1 GiB, 700 KiB for 4096 pieces.
- **Pointer hygiene** (from design 1): a fresh key and a new CDN object for every upload, never
  Desktop's 3-day reuse cache (`uploadAttachment.preload.ts:52, 74-91`); content type
  `application/octet-stream`; no file name, caption, blur hash or client UUID; `uploadTimestamp`
  kept. A pointer older than 25 days is treated as dead.
- The list is a hint. A wrong pointer fails Signal's MAC or `PIECE_ACCEPT`, and the piece goes to
  repair. Its F record and opening are checked by `OPEN_PIECES`.

### 3.6 Wire

```proto
message ZrdtServeRequest { /* 1-5 as JOIN_PLAN §10.1 */ optional bytes storeId = 7; } // piece store id
message ZrdtServed       { /* 1-4 as JOIN_PLAN §10.1 */ optional AttachmentPointer sealedOnCdn = 5; }
```

Field 6 is left to TRANSPORT's `leaves`, which this plan does not use. Nothing else is new on the
wire.

## 4. `zrdtd`: the piece store

### 4.1 State

- A `CheckedStore` (group = the piece store id), with its audience table. Every entry in the
  table equals the descriptor's audience.
- **The descriptor:** channel id, A's digest (once bound), author, audience, N, k, L, torrent
  nonce, F's digest, and F's ordered digests (once known).
- **Slots:** digest → index, for accepted pieces.
- **The store blob `zrdtT4`:** `"zrdtT4"` ‖ descriptor ‖ slots ‖ the records as a `zrdtS2` blob.
  Piece bytes and openings stay with the host, as chat openings do (A4).
- **Unbound** (the author, before A exists) or **bound** (A known, so F and its want set are
  known).

### 4.2 Accept rules

These apply to every path that adds a record: `ACCEPT`, `ACCEPT_RECORD`, `ACCEPT_VIEW`,
`PIECE_ACCEPT`, `FINISH_PIECES`. They are checked in this order:

1. No opening: `NEEDS_OPENING`. This closes C5: a stored piece always had its bytes checked.
2. `openingMatches` fails: `BAD_OPENING`.
3. The author is not the descriptor's, `audienceOf` is not the descriptor's audience, or the
   header is neither a piece nor F: `BAD_PIECE`. A piece's index must be below N, its length
   exact, and its nonce `nonce_i`. F's file table must pass `btFiles`, otherwise `BAD_MANIFEST`.
4. On a bound store, a digest that is neither F's nor `ordered[index]`: `IGNORED`. A relayed fake
   in the author's name never enters, so heads stay {F}.
5. Otherwise `CheckedStore.accept`, and the slot is recorded.

Also:
- `MERGE` and `SALVAGE` on a piece store: `BAD_REQUEST`. They would add records without openings.
- `SERVE` on a piece store is per-digest only; a catch-up gets `BAD_REQUEST`. Otherwise it is
  JOIN's `SERVE`, unchanged.
- `OPEN` of a `zrdtT4` blob trusts the slots as the device's own state, as `zrdtS3` trusts its
  audience table.

### 4.3 Ops (frame protocol 4; numbers provisional until TRANSPORT §8 settles)

| Op | Name | Request | Reply |
|---|---|---|---|
| `0x19` | `PIECE_STORE` | channel ‖ author `aci` ‖ torrent nonce | the store id |
| `0x1A` | `NEW_PIECES` | chat ‖ channel ‖ `aci` ‖ audience ‖ N ‖ k ‖ L ‖ nonce | `OK`: an unbound store (author) |
| `0x1B` | `PIECE_ACCEPT` | chat ‖ `u32` index ‖ bytes | `ACCEPTED` digest; `BAD_PIECE`; `IGNORED` |
| `0x1C` | `PIECE_OPENING` | chat ‖ `u32` index ‖ bytes | the opening, for `SERVE`'s held items; `BAD_PIECE` |
| `0x1D` | `FINISH_PIECES` | chat ‖ app manifest | F's record ‖ F's opening; `MISSING` (indices); `BAD_MANIFEST` |
| `0x1E` | `BIND_PIECES` | chat ‖ channel chat ‖ A's digest ‖ A's opening | `OK`; `BAD_REQUEST` |
| `0x1F` | `OPEN_PIECES` | chat ‖ channel chat ‖ A's digest ‖ A's opening ‖ F's record ‖ F's opening | ordered digests ‖ files; `BAD_MANIFEST`; `BAD_REQUEST` |
| `0x20` | `COMPLETE` | chat ‖ first ‖ count | `OK` digests in index order; `MISSING` indices |
| `0x21` | `FILES` | chat ‖ F's opening | files (name, path, offset, length, executable); `BAD_REQUEST` |

- **`BIND_PIECES`** checks four things: A is stored in the channel store with this opening, which
  passes `appHeader` for `"bt"`; `piecesOf` equals the descriptor; the store id is
  `PIECE_STORE(channel, A.author, nonce)`; `audienceOf` A equals the store's audience. It also
  checks that F is stored and that every stored record is F or a piece in F's ordered list.
- **`OPEN_PIECES`** makes the same checks against a fresh store, plus `hash F = manifest` and
  `openingMatches` for F. It returns the work data the host needs.
- New statuses: `0x0D` `BAD_PIECE`, `0x0E` `NEEDS_OPENING`, `0x0F` `BAD_MANIFEST`. `IGNORED`
  (`0x0B`) also becomes a reply to accept ops.

## 5. The author: share

1. `zbt add <paths> --group G` hands the paths to the fork. The fork's own dialog shows the name,
   size, file count and group. The app cannot share without it.
2. On confirm: the JOIN §4.1 enqueue snapshot. Then the layout, a random torrent nonce, and
   `PIECE_STORE`.
3. Upload every piece with a fresh key, paced (TRANSPORT §11). If an upload fails for good (413
   at that size, or a 428 challenge), there is no torrent and nothing is sent.
4. **Freeze** (JOIN §4.1): `AUDIENCE`, `NEW_PIECES`, then `PIECE_ACCEPT` for each piece (one
   hashing pass), then `FINISH_PIECES` with the file table.
5. Upload the piece list with a fresh key.
6. Build A (201, 210, 211, 212, 215). Then `COMMIT`, `LINKABLE`, `ACCEPT` into the channel, and
   `BIND_PIECES`.
7. Check that the Content is at most 64 KiB. Send A to the group by sender key, and 1:1 to the
   account's own devices. Persist.

**The freeze window** runs from step 4 to step 7: about 20 s per GiB of hashing, plus the list's
upload. A member added in it is not seated and is not sent A. A member removed in it stays seated
but is not sent A live, and responders answer only current members (JOIN §4.3). Later, a SHA-256
midstate op would hash the piece bytes before the freeze (§3.3) and close most of the window.

## 6. A member: fetch, repair, seed

### 6.1 Offered

A arrives live or by channel repair, and `ACCEPT` stores it in the channel (TRANSPORT §5.2). The
app gets `offered` with the name, size, file count, author and provenance. A relayed A shows
"relayed by …" until the author confirms it (A8).

### 6.2 Fetch

- **Policy.** Fetch automatically under 32 MiB (configurable); otherwise on a user action. In the
  official profile, fetching is the only automatic step: it is a CDN download, as stock Signal
  auto-downloads attachments.
- Download the piece list through A's pointer, using Signal's resumable download outside the
  message pipeline. Then `OPEN_PIECES`, which returns the ordered digests and the checked files.
- For each wanted index: download the piece, then `PIECE_ACCEPT`. `BAD_PIECE` is blamed on whoever
  supplied the pointer (here the author), shown to this receiver only. A 404, 403 or MAC failure
  sends the index to repair.
- **Selective download:** the files the user picks map to piece indices through the offsets.
  `COMPLETE` on those ranges says when they are done.
- **Complete:** `COMPLETE(0, N)` is `OK`, then `ACCEPT_RECORD` of F, and heads become {F}. The host
  writes the files from the checked piece bytes at the offsets `FILES` gave, under
  `<downloads>/<name>/`. Writes use `openat` with `O_NOFOLLOW`, and a target directory that
  contains a symlink is refused. The executable bit is applied only if the user allows it.
- **Resume.** Accepted pieces are durable in the store. Signal resumes partial downloads from an
  offset. `zbt recheck` re-runs `PIECE_ACCEPT` over the bytes kept.

### 6.3 Repair (JOIN's gap path, unchanged)

- **Request:** `ZrdtServeRequest{groupId, requestId, digests, storeId}`, sent 1:1. The digests
  come from `ordered` for the missing indices. Each request asks for at most 32 MiB of piece bytes
  (at least one piece), so a sealed reply always fits one attachment.
- **Whom to ask:** A's author first. Then current members seated in A's audience, which the
  requester reads from A's opening. At most 3 at once, on disjoint pieces. **Never anyone outside
  A's audience,** so no newcomer learns that a store exists.
- **Timeouts** (from design 1): 2 minutes plus size / 0.8 MB/s when an upload is needed. Then
  reassign. After a `BAD_OPENING` from a member, stop asking that member for this torrent.
- **Responder:**
  1. Check that the requester is a current member (JOIN §4.3).
  2. Find the store by `storeId`. If there is none, reply `ZrdtNotFound`.
  3. Call `PIECE_OPENING` for each wanted piece it holds, from kept piece files or the assembled
     files (piece i is bytes [i·2^k, …) of the stream).
  4. Run per-digest `SERVE` with those held items and seal (JOIN §4.3). If the sealed reply is over
     48 KiB (nearly always), upload it with a fresh key and send `ZrdtServed{sealedOnCdn}` 1:1.
- **Requester:** the JOIN §4.4 checks, then `ACCEPT_VIEW` into the piece store. Each entry gives
  `ACCEPTED`, `BAD_OPENING` (blame the responder, to this receiver only), `NEEDS_OPENING` (the
  responder lacks the bytes: ask the next member), or `IGNORED`.
- **Official profile:** each re-upload waits for the responder's user to click ("Carol asks for 3
  pieces (12 MiB) of trip: send?"). The private profile serves automatically.
- **Strict mode** (JOIN §5, per group): only the author repairs (`serve_strict`). The host passes
  its own piece digests as `live`.

### 6.4 F is lost

The piece list has expired, or the torrent is on-demand. Then request `hash F` with `storeId`.
The host takes F's record and opening from the unsealed reply, after the §4.4 checks, and calls
`OPEN_PIECES`. Lean checks `hash F` against A's commitment, so F's source does not matter.

### 6.5 On-demand mode

A without `pieceList`: the author uploads nothing at publish, and every fetch goes through
§6.4 and §6.3. Use it for large libraries on private servers, where members pull what they
choose. It costs one sealed upload per requester. It adds no mechanism: it is the expiry path,
used from the start.

### 6.6 Seed, retain, share again

- **Seeding** means keeping the piece store and the bytes, as piece files or as the assembled
  files. `zbt retain <id> pin|cache|drop`. `drop` closes and deletes the store, and A stays in the
  channel.
- **Share again** (to newcomers, on purpose): `zbt share <id> [files]` makes a **new torrent**
  with TRANSPORT's `sharedFrom` set. It has a fresh nonce, the current audience, a fresh hash and
  fresh uploads, from the sharer's checked files. It needs the fork's dialog, which says "you
  shared … with …". A subset of files makes a smaller torrent.
- **No deduplication** in v1: a member downloads a new torrent's pieces through its own list, even
  if it holds the same bytes from an older torrent. Deduplication would not leak content (§7,
  R1(c)), but it would leak timing, and v1 does not need it.

### 6.7 Export

`zbt export-torrent <id>` writes a local BEP 52 `.torrent` from the completed files, with design
1's tested root code: no ACI, no group, no "created by". It warns that the infohash fingerprints
the files. This is a user action and outside zrdt's guarantees.

### 6.8 The app process

`zbt` (CLI, optionally a Files panel) talks to the fork over TRANSPORT's socket with app tag
`"bt"`. It sees only events and checked files: `offered`, `progress`, `bad piece (from whom)`,
`complete (paths)`, `unavailable`. It never sees pointers, openings, nonces or `SERVE`. So a
buggy or hostile app cannot leak older content, and it cannot share without the fork's dialog.

## 7. How R1, R2 and R3 hold

**R1: a later joiner gets no older data unless someone shares it on purpose.** Each row is an
attack and what stops it.

| Attack | What stops it |
|---|---|
| (a) A channel catch-up returns an older A (name, descriptor, list pointer) | `serve_content`: A's opening goes only to accounts its own audience seats. A newcomer gets boundary digests (JOIN §6). |
| (b) Older piece bytes, or an older file table, through repair | A piece's bytes are its opening. `serve_content` releases it only under its own audience, which is A's (`pieces_follow_announcement`). C4 checked this on the shipped code. |
| (c) **Content-addressed pull:** a newcomer names a file the group shared earlier, to get it or to test whether the group had it | Impossible by construction. To name a piece he needs its digest, salted by a secret store id. To make his own torrent he needs the bytes. A member who fills his store from an older copy fills it with exactly the bytes he committed, which he already has. No host bookkeeping is involved. |
| (d) CDN pointers are bearer tokens | Piece pointers sit only in the piece list, and its pointer only inside A's committed body. They travel exactly where A's opening goes: the live send (recipients ⊆ audience) or `SERVE`, sealed. |
| (e) Desktop's 3-day reuse hands out an older object and links two torrents for the server | A fresh key and a new object for every upload (host duty). |
| (f) Availability messages show older activity | There are none. Nothing about pieces goes to the group except A. |
| (g) A newcomer learns that an older torrent exists | Store ids come from a nonce he cannot see. Repair asks only A's seats. He sees older A's only as opaque digests. |
| (h) A large sealed reply on the CDN | Its bytes are sealed to the checked key. The pointer opens nothing for anyone else. |
| (i) A key swap between the check and the send | The seal (JOIN §4.3). C4: a swapped key gets no content from `SERVE`. |
| (j) A server-asserted join revision | Never read (JOIN H3). |
| (k) A member added while the author hashes | Not seated and not sent A. He gets the torrent only through "share again". |
| (l) Relayed fake records in the author's name | `IGNORED` on a bound store: they are not in F's ordered list. |
| (m) The app auto-shares ("seed everything to new members") | The app has no pointers and cannot share without the fork's dialog (§6.8). |

**R2: authenticity only of the designated-verifier kind.**
- Nothing new signs or MACs. Commits, store ids, nonces and ordered digests are hashes that
  anyone with the inputs can recompute. The seal gives confidentiality only (JOIN §4.3).
- Authenticity comes from Signal's deniable channels. A is live from its author, or relayed until
  the author confirms it (`authorConfirmed_sound`). F is bound by A's commit, and pieces by F. A
  relayed piece is exactly as good as the author's, and shows nothing about who sent it.
- Banned, because each would break R2: signed torrents (BEP 35, BEP 46), requiring signed git
  objects, keeping sender-key messages, broadcast per-member tags (JOIN §10a), and an ACI or group
  id in an exported `.torrent`.
- **Residuals, Signal's own:**
  - The server logs who uploaded each object. Its logs plus a member's device tie uploads to
    accounts, and repair re-uploads add more such events.
  - A manifest digest read aloud pins the files, as any compare code does (JOIN §7.4).

**R3: reuse Signal first.**
- **Reused:**
  - one sender-key send per torrent (`sendContentMessageToGroup` takes any Content);
  - pairwise sealed-sender sessions for repair;
  - the CDN: encrypt once, upload once, tus and resumable uploads, resumable downloads, and MAC
    and digest checks;
  - Signal's 24 h retry for A;
  - Signal groups as audiences;
  - libsignal's primitives for the seal;
  - and zrdt's own gap detection and `SERVE`, both unchanged.
- **Added, each for a gap:**

  | Addition | The gap it fills |
  |---|---|
  | Piece stores and the piece check | Signal checks whole attachments only, and has no notion of completeness across several attachments. |
  | Re-uploads between accounts | Signal's backfill works only between one account's own devices. |
  | The Lean file table | Paths come from another account. |
  | `NEEDS_OPENING` | Today's `ACCEPT_RECORD` takes records without content (C5). |
  | The pacer and profiles | Desktop treats 413 as a rate limit and never retries it, and the terms of service forbid bulk and automatic messaging. |

**Threat model.** The server and the network are the adversary.
- **They can:**
  - drop, delay or withhold A or pieces, which shows as a gap and is repaired
    (`withheld_tail_undetectable` still applies to the newest A);
  - delete or expire CDN objects early, which is repaired;
  - corrupt bytes, which fails Signal's MAC and is repaired;
  - see uploaders, padded sizes, timing, download IPs and counts, and who repairs for whom;
  - swap keys, which the seal covers.
- **They cannot:**
  - inject records (Signal authenticates senders, and a bound store takes only F's list);
  - change bytes undetected (`openingMatches`, unless SHA-256 has a collision);
  - read content;
  - make an honest member release a piece to an account A did not seat.

Members are honest or attributable. Wrong bytes are caught per piece and blamed on whoever
supplied them, to the receiver only. A malformed torrent (bad indices, lengths or paths) is
refused and attributable to A's author. A huge declared size is checked by the user against free
disk space before the fetch. Closed groups only.

## 8. Theorems

Two kinds, as in PLAN_HUMANS §5.
- **Running-code theorems** are about the functions `zrdtd` runs (Mathlib-free, `core/`). They stop
  bugs from leaking.
- **Spec theorems** (`Crdt/Merkle`) say what a store means. The advertised ones are stated over
  `CheckedStore` in `Api.lean`.

### 8.1 Reused unchanged (a piece store's record part is a `CheckedStore`)

- **Spec, advertised:**
  - `CheckedStore.abs_accept`: `ACCEPT_RECORD` of F returns `MISSING` with exactly the absent
    pieces (C1);
  - `CheckedStore.fetched`: a store holding F holds everything F reaches;
  - `CheckedStore.agree`: piece stores with heads {F} hold the same records, or there is a
    collision;
  - `CheckedStore.confirmed`, `CheckedStore.no_collision`, `Zrdt.encode_injective`;
  - `CheckedStore.serve_content` and `CheckedStore.serve_content_complete`;
  - `CheckedStore.agree_rel`, for newcomers' channel stores.
- **Spec, not advertised:** `reach_implies_held`, `authorConfirmed_sound`, the four limits
  (`Chat.lean`), and `Rel.lean`, for the channel.
- **Running code:**
  - `Serve.serve_content`, `serve_content_complete`, `serveOpening_spec`, `serve_strict`,
    `serve_authorCopy`, `audience_bound` (`Serve.lean`);
  - `run_serve_content`, `acceptRecord_accepted`, `accept_accepted`, `acceptView_sound`,
    `acceptView_accepted`, `run_acceptView`, `commit_openingMatches` (`Proto.lean`);
  - `openingMatches_spec`, `commitWithOpening_matches` (`Commit.lean`).

`SERVE`'s code, and every theorem about it, stay as on origin/join.

### 8.2 From TRANSPORT (to prove there, needed here)

`opening_bound` (two openings that match one commit are equal, or SHA-256 has a collision),
`appOpening_lasting`, and `run_accept_app`, extended with field 215.

### 8.3 New, running code (`core/Zrdt/Pieces.lean`, `core/Zrdt/BtManifest.lean`)

- **`run_piece_accept`.** If `PIECE_ACCEPT(i, bytes)` replies `ACCEPTED d`, then the store holds a
  record at d with the store's group, the descriptor's author and no links. The opening built
  from (`nonce_i`, bytes, i, the audience) matches it, `i < N`, `|bytes| = pieceLen i`, and the
  slot of d is i. On a bound store, also `d = ordered[i]`.
- **`run_accept_pieceStore`.** Every accept op stores a record only under the rules of §4.2.
  Otherwise it replies `NEEDS_OPENING`, `BAD_OPENING`, `BAD_PIECE`, `BAD_MANIFEST` or `IGNORED`,
  and nothing changes. `MERGE` and `SALVAGE` refuse piece stores.
- **`pieceStore_inv`,** kept by every op and by `OPEN`:
  - every stored digest has a slot or is F;
  - every audience-table entry is the descriptor's;
  - on a bound store, every stored record is F or in `ordered`.
- **`bindPieces_bound`, `openPieces_bound`.** A store becomes bound only under the four checks of
  §4.3, plus `hash F = manifest` and `openingMatches F`.
- **`pieces_follow_announcement`** (advertise). For a bound store, a stored record r and any
  opening o that matches r: `audienceOf o = audienceOf (A's opening)`, or SHA-256 has a
  collision. The proof is `pieceStore_inv` plus `audience_bound`.
  - Its corollary **`serve_pieces`**: `SERVE` on a piece store releases a piece only to an
    account A's audience seats, under the checked key.
  - With `serve_content_complete`: whenever A's audience seats the requester, a held piece does
    go. Piece content goes exactly where A's content goes.
- **`complete_iff`.** `COMPLETE(first, count) = OK ds` exactly when, for every i in the range,
  `ordered[i]` is stored with slot i, and then `ds` lists those digests. And F is stored exactly
  when `COMPLETE(0, N)` is `OK`.
- **`assemble_unique`** (advertise). Take two stores bound to the same A, both complete, with
  openings that match their records. They hold the same piece bytes at every index, or SHA-256
  has a collision. Proof: F's digest is the same, so F's record and opening are the same (or a
  collision, `opening_bound`). So `ordered` is the same, each piece record is the same, and each
  opening is the same. It is a composition, with no induction over a Merkle tree.
- **`btFiles_safe`.** Every path `FILES` returns passes `safeComponent`, with 1 to 16 components.
  The list is strictly sorted, and no path is a prefix of another.
- **`btFiles_tile`.** The offsets are the running sums of the lengths, and the lengths sum to L. So
  every byte written comes from exactly one checked piece range.
- **`run_files`, `run_complete`, `run_serve_pieceStore`.** The ops answer exactly as the functions
  above. A catch-up on a piece store is `BAD_REQUEST`.
- **Later, `midstate_commit`** (with the midstate op): finishing a midstate with the remaining
  bytes equals `commit` over the whole input.

### 8.4 New, spec side (`Crdt/Merkle/Api.lean`)

Advertised restatements over `CheckedStore`, in the style of `CheckedStore.serve_content`:
`CheckedStore.pieces_follow_announcement` and `CheckedStore.assemble_unique`. That is +2 to the
advertised list, and the axiom gate and the Comparator challenge follow (§13, question 5).
`btFiles_safe` stays a pinned obligation, not advertised.

### 8.5 Tests (`#guard` and named examples, as JOIN §7.1)

- Port C1 to C6 from `/tmp/zrdt-apps-bt2/PieceCheck.lean`.
- A newcomer gets no piece opening, per-digest or catch-up. A seated member under a swapped key
  gets none.
- No opening gives `NEEDS_OPENING`. An extra field, a wrong index, length, nonce, audience or
  author gives `BAD_PIECE`. A flipped byte gives `BAD_OPENING`. A record outside `ordered` gives
  `IGNORED`. `MERGE` into a piece store gives `BAD_REQUEST`.
- Paths `..`, `a/b`, a NUL, a file `x` beside `x/y`, unsorted files, and lengths that do not sum
  to L all give `BAD_MANIFEST`.
- Ordered digests that are not exactly F's links give `BAD_MANIFEST`.
- The same file in two torrents gives different piece digests (salting).
- One satisfiable example per new theorem, and one bad output each one rules out.

### 8.6 Host duties (trusted, like `live` and disown in A8)

- **Uploads:** a fresh key per upload, never the reuse cache.
- **Pointers:**
  - piece pointers only in the piece list;
  - the list's pointer only in A's committed body;
  - sealed-reply pointers only in `ZrdtServed` to the header's ACI.
- **Content:**
  - give `SERVE` only openings from `PIECE_OPENING`;
  - give the app only bytes that passed `PIECE_ACCEPT` or `ACCEPT_VIEW`, at `FILES` offsets.
- **Repair:** ask only current members seated in A, and never send a `storeId` to anyone else.
- **Sharing:** only from the fork's dialog.
- **Sending:** check sizes before sending, and pace.

`zrdtd` cannot see where bytes or pointers go. Unlike design 1, no host duty decides *which*
bytes may go to whom: Lean decides that.

## 9. Limits, and what is honest to claim

**We can claim:**
- **Verified completeness and integrity.** An app reports a torrent complete only when every
  piece matches the author's commitment. Two members who completed it hold the same bytes, or
  SHA-256 has a collision (`run_piece_accept`, `complete_iff`, `assemble_unique`).
- **Exact gaps, and repair.** A missing piece is named exactly (`abs_accept`) and fetched again
  from any member who kept it.
- **Audience-gated content.** Every byte of a torrent, its file names, and the pointers that open
  its CDN copies go only to accounts the author's client addressed at share time, under the keys
  it checked. This is proved for `SERVE` (`serve_content`, `pieces_follow_announcement`). The seal
  and the pointer rules are host duties.
- **Nothing for late joiners,** not even the torrent's existence, unless a member shares it again.
- **No transferable proof** of who shared what.
- **TCP-like** in reliability, retransmission, integrity and completeness.

**We must not claim:**

| TCP | zrdt torrent |
|---|---|
| Ordered byte stream | No: pieces arrive in any order; files are written when their pieces are in |
| ACK | None per piece. The author does not learn who completed. |
| Retransmission | Yes: Signal resumes transfers; zrdt repairs by per-digest `SERVE` and sealed re-uploads |
| Checksum | Stronger: a salted SHA-256 commitment per piece |
| Flow and congestion control | None; a pacer for Signal's limits |
| Latency bound | None: store-and-forward, and repair may wait for a person (official profile) |

- **Throughput:** Signal's upload limits set the pace. With the open-source defaults, after a
  1 GB burst, about 1 MB/s per uploading account: 1 GiB in about 0.3 h, 16 GiB in about 4.8 h.
  Production values are unknown.
- **No swarm:** repair parallelism is at most 3 members. Each re-upload is sealed to one requester,
  so after the CDN copies expire, every late fetcher costs one full upload.
- **Availability:** about 30 days on the CDN. After that, only while a seated member keeps the
  bytes. Stock phones never hold pieces.
- **No metadata privacy from the server:** it sees uploaders, padded sizes, the shape of a share
  (N uploads, a list, a group send, N downloads per fetcher), download IPs, and who repairs for
  whom.
- **No smaller audience** than the Signal group, and at most 256 members.
- **No BitTorrent interop:** no peer wire, tracker or DHT. Export is local and display-grade.
- **Costs in `zrdtd`:**
  - about 50 MiB/s per hashing pass;
  - `SERVE` makes three passes per released piece (measured);
  - peak memory is about ten times the piece size;
  - about 165 B of state per piece;
  - one open store per torrent being fetched or seeded.
- **Official servers:** only small, user-started transfers (terms of service, rate limits). Real
  use needs the mock server (attachments in RAM, which caps demo sizes) or a self-hosted server
  (an infrastructure project).
- **Pending from JOIN:** the relative-store restatements of the advertised theorems (JOIN §7.3),
  which newcomers' channel stores rely on.

## 10. Effort and build plan

Prerequisites:
- JOIN stage 1, whose core is on `join`;
- JOIN stage 2 (the fork's `SERVE`, seal and §4.4 checks), needed for repair;
- JOIN stage 3 (the relative store), needed for newcomers' channels;
- TRANSPORT's channels and Content 205.

Estimates are in agent-days.

| Stage | Work | Days |
|---|---|---|
| B0 | **Shared with TRANSPORT:** `App.lean` (`channelId`, `appHeader` with field 215, `opening_bound`, `appOpening_lasting`, `run_accept_app`), `CHANNEL`, `NEW_CHANNEL`, `zrdtS4`. | 2 |
| B1 | **`Pieces.lean`:** descriptor, `piecesOf`, `nonce_i`, piece and F headers, accept rules, the 9 ops, `zrdtT4` with `encode_reopens`, statuses, C1–C6 ported. Theorems: `run_piece_accept`, `run_accept_pieceStore`, `pieceStore_inv`, `bindPieces_bound`, `openPieces_bound`, `pieces_follow_announcement`, `serve_pieces`, `complete_iff`, `assemble_unique`, `run_serve_pieceStore`. | 3–4 |
| B2 | **`BtManifest.lean`:** the parser, `safeComponent`, order, prefix-freedom, tiling, `FILES`. Theorems: `btFiles_safe`, `btFiles_tile`, `run_files`. | 1 |
| B3 | **`Api.lean`:** the two advertised restatements, their examples, the axiom gate. | 1 |
| B4 | **Fork transport base, shared with git:** Content 205 send and receive, the own-device copy, a saved send type, fresh-key uploads that skip the reuse cache, direct resumable downloads, the pacer, `sealedOnCdn`, the socket. | 8 |
| B5 | **Fork, piece stores:** the manager, raw uploads before the freeze, the commit loop, the piece list, the fetcher driven by `OPEN_PIECES` and `COMPLETE`, the repair scheduler (`storeId`, A's seats, 3 in parallel, timeouts, blame), profiles and consent prompts, retention, safe file writes. | 6 |
| B6 | **`zbt`:** the CLI (add, ls, get, status, share, retain, recheck, export-torrent), the manifest builder with the same path rules as a pre-check, an optional Files panel. | 3 |
| B7 | **Mock harness:** 3 to 5 members; CDN deletion forcing repair; injected 413, 429 and 428; a newcomer; a garbage piece; a key change mid-request; restart and resume. | 2–3 |
| B8 | **Last, only with kejace's approval:** Comparator, `lake check`, leanchecker. | — |

- **Totals:** Lean about 7 to 8 days (B0–B3); fork and app about 3.5 weeks (B4–B7). Everything is
  about 5 weeks after JOIN stage 2, with B0 and B4 shared with git.
- **Demo subset,** about 2 weeks after JOIN stage 2: eager publishing only, at most 1 GiB, one
  channel, the CLI, the mock server, strict repair (author only), no export.
- **Later:** the SHA-256 midstate op (closes the freeze window); retract records; 1:1 shares;
  deduplication; a `SERVE` memo (one hashing pass instead of three, with one equation lemma);
  public-torrent import (§13, question 2).

## 11. Design history

### 11.1 Design 1, "zbt" (not chosen)

**What it proposed.** One announce record per torrent:
- the manifest in the committed body;
- one BEP 52 (root, length) BlobRef per file, kept unsalted so the derived infohash matches public
  torrents;
- pieces of any size 2^j leaves, sent as attachments, each with a carrier (pointer plus Merkle
  proof) outside the commitment, checked by `CHECK_PIECE`.

Gating:
- `SERVE` gains `have` and `carrier` entries, and `GRANTS`;
- **the via rule:** a member releases pieces of record r only if it got them through r. This is
  host state, passed to `SERVE`.

Also:
- bundle carriers for many small files (the upload-form limit);
- have probes;
- lazy publishing, with re-uploads shared among concurrent requesters;
- partial replies;
- a dead-pointer list;
- per-16 KiB checks.

**Why not.**
1. **Unsalted content addresses create the attack** that the via rule must then stop: a newcomer
   names a known root. The via rule is host bookkeeping, so `serve_blobs` can only prove "released
   ⊆ what the host said was via r". One host bug reopens R1. In design 2 the attack has no
   handle: commitments are salted, and naming a piece requires the bytes.
2. **`SERVE` changes.** New entry kinds re-open `serve_after`, `serve_boundary`, `serve_abs`,
   `serve_heads`, `serve_closed`, `serve_tight` and `ServeAbs.lean`.
3. **Proof risk.** `assemble_root` and `pieceRoot_slice` are inductions over ByteArray slices.
   `checkPiece_sound` also needs an exact-length rule (design 1 found this) to avoid a
   "no preimage of zero" assumption.
4. **More protocol.** `GRANTS`, `CHECK_BUNDLE`, `haveOnly`, `dead`, `sequential`, `liveRanges`,
   `more`, a per-record upload queue, a multi-holder scheduler.

**What we kept:**
- the Lean file table and safe paths (`torrentFiles_safe`, now `btFiles_safe`), and safe file
  writes;
- the app never sees pointers, and shares only through the fork's dialog;
- the official and private profiles with consent;
- pointer hygiene and the 25-day staleness;
- the scheduler's timeouts and blame;
- `.torrent` export with its tested BEP 52 code;
- resume semantics.

**What we gave up:**
- **One re-upload shared by several late requesters.** Each sealed reply is per requester. Within
  30 days, everyone shares the author's uploads anyway.
- **BEP 52 file identity in the commitment.** It is still available at export.
- **Per-16 KiB checks.** Signal's MAC already catches corruption in transit, and a bad piece is
  re-fetched whole.
- **Have probes.** Asking, and getting `NEEDS_OPENING`, costs one round trip.
- **Lazy publishing.** On-demand mode (§6.5) covers it at a per-requester cost.

### 11.2 Design 2, "bt/R" (chosen)

What it contributed, as it stands:
- the announcement and piece-store shape;
- bytes inside openings;
- repair as the unchanged gap path;
- `pieces_follow_announcement` and `assemble_unique`;
- the C1–C6 checks on the shipped code;
- `NEEDS_OPENING`.

### 11.3 Changes the judge made to design 2

| Change | Why |
|---|---|
| A repair asks for at most 32 MiB of piece bytes (at least one piece). Design 2 allowed 4 pieces of up to 64 MiB. | A sealed reply must fit one attachment (97.49 MiB). Memory is about 10× (measured). |
| Ordered piece digests in F's opening (field 225), checked against F's links. | Design 2 had no index-to-digest binding in Lean. Repair of a selected file needs digests by index, and `PIECE_ACCEPT` can check the exact position. |
| Deterministic nonces `nonce_i`, computed by `zrdtd`. | The secret store id already salts every commit. Responders rebuild openings from bytes alone, and the list carries no nonces or commits. |
| Bytes first in piece openings. | Enables a later midstate op to close the freeze window with no wire change. Today's code accepts this order (judge's bench). |
| No layer records; N ≤ 4096; L ≤ 256 GiB. | Removes a record kind and its rules. Larger torrents are impractical on Signal anyway. |
| `MERGE` and `SALVAGE` refuse piece stores. | They would add records without openings, around the C5 fix. |
| The descriptor in a transport field 215, not in the bt body. | App-neutral, so git can use piece stores. |
| `FINISH_PIECES` builds F in Lean, and `FILES` re-derives the file list. | The host never builds F's opening or links. |
| The `SERVE` memo moved to "later". | Measured: 3.8 s per 64 MiB released, small next to the upload time (about 67 s at 1 MB/s). `SERVE` stays byte-for-byte as shipped. |

## 12. Review brief

Please try to break these, in this order:

1. **The R1 chain for bytes:** `serve_content`, plus `pieces_follow_announcement`, plus the seal.
   Find any path that moves piece bytes, F's file table, or a pointer outside it: exports, the
   own-device copy, Signal's retry, the piece list, sealed replies on the CDN, logs, the app
   socket.
2. **The content-addressed pull (§7, (c)).** Can a newcomer who holds, or only knows the hash of,
   an older file get it, or learn that the group had it? Try relayed records, dedup bugs, guessed
   store ids, and timing.
3. **Accept-rule coverage (§4.2).** Is there any path that stores a piece record without checked
   bytes? Consider `ACCEPT`, `ACCEPT_RECORD`, `ACCEPT_VIEW`, `PIECE_ACCEPT`, `FINISH_PIECES`,
   `OPEN` of `zrdtT4`, `MERGE` and `SALVAGE`.
4. **Ordered digests vs links (§3.4).** Repeats, short lists, a list that differs from the links,
   an index that does not match.
5. **Deterministic nonces.** Can anyone outside A's audience test a guess of a piece's bytes?
   Consider what reaches a newcomer: boundary digests of A, never piece digests.
6. **The freeze window (§5),** and members removed or added inside it.
7. **Sizes and limits:** 64 KiB Content; at most 32 MiB per sealed reply; 700 KiB lists; F at up to
   131 KB as a record; the 413 and 428 handling; zrdtd memory.
8. **Layering.** GIT_PLAN.md uses TRANSPORT's BlobRefs, carriers and via rule, and this plan does
   not. Can a git pack ride a piece store, with `CHECK_PACK` run over the assembled stream? What
   would the git app lose (for example, `GRANTS` and shared re-uploads)? One bulk mechanism or two
   (§13, question 1)?
9. **What is not checked here:**
   - no fork code exists;
   - Signal behaviour is inherited from the fact checks and TRANSPORT, with stock iOS's handling
     of Content 205 still unverified;
   - the new theorems are statements, not proofs;
   - production rate limits are unknown.

## 13. Open questions for kejace

1. **One bulk mechanism.** GIT_PLAN.md carries packs as TRANSPORT blobs (carriers, via rule, new
   `SERVE` entries), and this plan uses piece stores. The choices:
   - (a) **Both use piece stores.** We recommend this: one R1 argument, and it is the shipped
     `serve_content`. The git plan would need its pack check run over a piece store's assembled
     stream.
   - (b) **Git keeps blobs and the torrent keeps piece stores.** Two mechanisms and two R1
     arguments, and the via rule stays in the trusted base.
   - (c) **The torrent moves to blobs.** That is design 1, with the costs of §11.1.
2. **Public-torrent interop.** Do you want to import a public v2 `.torrent` and check the group's
   copy against its infohash? If yes, a later stage adds design 1's BEP 52 check as a local
   verification. It would not touch the R1 gate.
3. **Official servers.** On Signal's own servers, should the torrent app be capped (about
   100 MiB per torrent, every re-upload clicked), or not be offered at all, leaving the mock and
   self-hosted servers?
4. **On-demand mode** (§6.5): in v1, or later?
5. **Advertise +2** in `Api.lean` (`pieces_follow_announcement`, `assemble_unique`)? Comparator
   runs only as the last step, with your approval.

## Open issues from the adversarial review (not yet folded in)

Two breakers attacked this plan after it was written: breaker 1 as the malicious server and
network, breaker 2 on R1 and R2 for piece bytes. Neither found a fatal break: SERVE is unchanged,
pieces carry A's audience, and no route gave a newcomer older piece bytes. The revise step that
would have folded their findings into §0–§13 did not run, so **the sections above still contain
the claims these findings contradict** (notably §0, §5, §7, §8.6 and §9). Both breakers worked
against join `acbd70a` (protocol 3; breaker 2 checked that `serve` is identical on `9637904`) and
ran no Comparator, `lake check` or leanchecker.

Evidence: scratch files under `/tmp` (not in any branch, may be gone after a reboot). Signal
source files are named as the breakers cited them, in Signal-Desktop v8.33.0 (a read-only copy is
at `/tmp/zrdt-spike-fork/sd-v8.33.0`) and Signal-Server. "Plan reading" means the breaker argued
from this document and the shipped Lean, without a test. Attack numbers count from 1 in each
breaker's report.

### Major

**T-M1. A member removed during the freeze, then re-added (or served by a lagging responder), gets
the whole torrent.** (Breaker 1, attack 1; breaker 2, attack 1; both major.) §5 fixes the audience
at step 4; COMMIT/ACCEPT are at step 6 and the send at step 7. In between come the hashing (about
87 min at 256 GiB at 50 MiB/s) and the piece-list upload, which the server can stretch with 429s
and 428 challenges, and which a laptop sleep or restart extends without bound. A member removed in
that window stays seated in A. "Responders answer only current members" does not protect: (a) once
re-added she is current, A was accepted after her removal so `since` does not reach it, and both
catch-up and per-digest `SERVE` release A's opening (piece-list pointer valid 30 days, store nonce,
file table), and per-digest repair releases every piece (`pieces_follow_announcement`); (b) with no
re-add, the server delays the removal at one responder only, whose later record links A, and that
responder serves A. Breaks JOIN §6.5 ("none from the gap"). The window cannot be made atomic like
JOIN's chat freeze: Desktop's per-conversation queue is serial with a 30-minute task timeout, and
group updates use the same queue.
- Fix: in the same `queueJob` that runs COMMIT and ACCEPT and enqueues the send, re-read
  `membersV2` and every seated member's identity key just before COMMIT, and again before each send
  attempt while nothing has been sent. If a seated account left or a key changed, discard A and
  freeze again (AUDIENCE, a fresh unbound piece store, `PIECE_ACCEPT`, `FINISH_PIECES`, a new piece
  list); the step-3 CDN uploads carry no audience and are reused. Accept A into the channel store
  only when the first send attempt goes out, so a discarded A is never linked. Cap the window (for
  example re-freeze if step 5 or 7 exceeds about 10 minutes); never resume a freeze after a restart
  or sleep. Move the SHA-256 midstate op into v1 so a re-freeze re-hashes only the audience tail.
  Apply the same re-check to JOIN's chat retries (§4.1), which have the narrower form of this gap.
- Evidence: `/tmp/zrdt-apps-breaker1/bt/ReaddLeak.lean` (every `#guard` passes on the shipped
  `Serve.serve`); `/tmp/zrdt-apps-breaker2/Readd.lean`, run on the build in
  `/tmp/zrdt-apps-btjudge/core`; `conversations.preload.ts:4021` (PQueue concurrency 1),
  `TaskWithTimeout.std.ts:83-84` (30 min), `groups.preload.ts:3130`.

**T-M2. Signal's saved-proto retry gives a swapped key A's pointer, and so the whole torrent.**
(Breaker 2, attack 11, major; breaker 1, attack 3, minor.) TRANSPORT §3.3 saves Content 205 for
Signal's retry. Within the sendLog's 24 h, a server that swaps a seated member's key and sends a
`DecryptionErrorMessage` as that member makes Desktop re-send A to the current (server's) key; a
409/410 during step 7 does the same. The server reads A, then the piece list, every piece and the
file table, up to 256 GiB, bypassing the seal §7(i) relies on. Stock Signal exposes one message;
here one message opens a whole torrent. Also contradicts §9's "under the keys it checked".
- Fix: send Content 205 with a send type that is not saved to the sendLog and repair A only through
  sealed, key-checked `SERVE`; in the fork's Content 205 path, compare each recipient's identity key
  at encryption time with A's seat tag and skip any recipient whose key differs or who is not
  seated (JOIN §4.1's "a key change forfeits the message"), covering 409/410 re-fetches.
  Alternatively keep the piece-list pointer out of A and deliver it only in sealed `SERVE` replies.
  Otherwise list it as a residual in §7 and §9. (The git breakers found the same; it is a TRANSPORT
  fix shared by both apps.)
- Evidence: `handleRetry.preload.ts:192-249`, `getSentProtoByRecipient` with the 24 h sendLog
  (`Server.node.ts:1703`).

**T-M3. Repair amplification and congestion collapse, which the server can trigger for free.**
(Breaker 1, attack 2.) Each re-upload is sealed to one requester; responders have no queue, no
"accepted" frame and no cancel; the requester's timeout (2 min + size / 0.8 MB/s, then reassign)
assumes a dedicated 0.8 MB/s, but Signal meters attachment bytes per uploading account (1 GB burst,
then 1 MB/s), shared with the user's own photos. The server deletes the CDN objects right after A
is sent (or holds A past 25 days) and every member enters repair, asking the author first; five or
more concurrent 32 MiB requests exceed the timeout, requests are reassigned to members who do not
hold the bytes and come back, and timed-out uploads still finish. A 1 GiB torrent in a 100-member
group needs at least 99 GiB of sealed uploads, about 28 h, while the author's normal attachments
get 429s and the account looks like bulk automation (428 challenges, ToS risk). The same happens
with no adversary when several late fetchers arrive after CDN expiry.
- Fix: one sealed upload at a time per responder account; answer each request at once with a tiny
  1:1 `queued{rid, position, eta}` frame and run the requester's timeout from that ETA; cancel a
  request with `cancel{rid}` before reassigning it; a per-(requester, torrent) serve budget (for
  example each piece at most twice per requester per 24 h); pace repair below the account limiter,
  leaving headroom for the user's own attachments; if many piece objects 404 within 25 days of
  upload, stop automatic repair and tell the user the CDN is deleting early. Optional: one shared
  fresh-key re-upload per piece, its pointer only inside sealed replies in which `SERVE` released
  that piece's digest to that requester (cuts M-1 uploads to 1, at the cost of one host rule).
- Evidence: Signal-Server `RateLimiters.java` (ATTACHMENT_BYTES), `AttachmentControllerV4`;
  Desktop sends `uploadSize`.

**T-M4. A forged or name-colliding announcement is fetched automatically and overwrites existing
files.** (Breaker 2, attack 2.) Member X forges A' with author = Y and the name of Y's genuine
torrent ("contract-v3"), at most 32 MiB, with X's own piece list, and links it from his live
record; gap repair asks X. `ACCEPT_VIEW` accepts any addressed entry whose opening matches (no
filter by `wanted`); §6.2 fetches automatically under 32 MiB with no provenance condition, and
writes under `<downloads>/<name>/` with nothing said about existing files. Y's files are silently
replaced; "relayed by X" exists only in the UI. Honest users hit it too: two torrents named "photos"
overwrite each other's files and seeding from the first stops.
- Fix: auto-fetch only an A that `CLASSIFY` reports `confirmedByAuthor`; a relayed A needs a click.
  Write each torrent into a new directory created with `mkdirat` that fails if it exists (with a
  short A-digest suffix); open files `O_CREAT|O_EXCL|O_NOFOLLOW`; never overwrite.
- Evidence: plan §6.2; `core/Zrdt/Proto.lean` `checkEntry`/`acceptView` (around lines 1153-1260 as
  cited; re-check against protocol 4, which changed per-digest boundary admission but not this).

**T-M5. Case- and Unicode-colliding paths show macOS users different files from Linux users.**
(Breaker 2, attack 3.) `btFiles` compares paths byte by byte, so `Report.pdf` / `report.pdf`, or
NFC `é` / NFD `e`+U+0301, are distinct and sorted; on default APFS (case- and
normalization-insensitive; the demo runs on a MacBook) and on Windows they are one file and the
later write wins. A misbehaving author puts different contents under the two names; Mac members get
one document, Linux members two, with COMPLETE OK, heads = {F} and matching compare codes.
`assemble_unique` is about piece bytes, not files on disk, so §9's "two members who completed it
hold the same bytes" gives false assurance. Windows adds trailing dot or space, `:` (alternate
streams) and reserved names (`CON`, `NUL`).
- Fix: `btFiles` also rejects any two paths, and any path-prefix pair, equal after Unicode NFC plus
  case folding, and rejects names Windows cannot hold. With `O_EXCL` writes (T-M4), any remaining
  collision is an error, not an overwrite.
- Evidence: plan §3.4, §9.

### Minor

**T-m1. The server sets the size caps.** (Breaker 1, attack 4.) `global.attachments.maxBytes` and
`maxReceiveBytes` are remote config and the upload form returns 413 above its own limit. Below about
67 MiB padded, 64 MiB-piece torrents cannot be repaired after CDN expiry; below about 34 MiB, even
32 MiB sealed replies fail; a 413 on the last piece at step 3 discards hours of uploads. Fix: make
`sealedOnCdn` repeated (split a sealed reply into chunks under the current cap); read the cap at
publish and at repair time; on a 413 at step 3 keep the uploaded pieces and offer a smaller k.
Evidence: `AttachmentSize.std.ts`.

**T-m2. The server learns the file size precisely.** (Breaker 1, attack 5.) Full pieces are exactly
2^k bytes and only the last goes through the 1.05^k padding buckets, so L is known to about
±100 KiB for 1 GiB with 4 MiB pieces; that fingerprints known files and links a re-share to the
original. Sealed-reply sizes show how many pieces each responder serves; an F-lost reply shows the
file-table size. Fix: upload the last piece zero-padded to 2^k (`PIECE_ACCEPT` trims to the
committed `pieceLen`); pad sealed replies to a fixed size and the piece list to a bucket; state the
remaining leak, N·2^k, in §9. Evidence: plan reading.

**T-m3. A MAC failure triggers a full re-upload, and a poisoned partial file persists.** (Breaker
1, attack 6.) §6.2 repairs on a 404, 403 or MAC failure, so one corrupted byte turns a cheap
re-download into a sealed per-requester re-upload; Desktop's resumable download keeps the corrupted
prefix and resumes after it. Fix: on a MAC or digest failure, delete the partial ciphertext and
download once more from offset 0; repair only after a 404/403 or a second failure. Evidence:
`downloadAttachment.preload.ts` (the `finally` block and the "went over" check).

**T-m4. False blame through TOFU impersonation of a responder.** (Breaker 1, attack 7.) The server
swaps Carol's key before the request, then answers as Carol with a correctly sealed reply of bad
openings; §6.3 then stops asking the honest Carol. §4.4's "responder key unchanged since the
request" misses a swap made before the request. Fix: blacklist or blame only a responder whose key
has not changed since A was received or since the last safety-number verification; otherwise show
"unverified responder" and keep asking others. Evidence: plan reading.

**T-m5. Overclaim: a late joiner does learn that older torrents exist.** (Breaker 1, attack 8;
breaker 2, attack 4.) §0, §7(g) and §9 say "not even the torrent's existence". The bt channel holds
only announcements and every new A links the channel's heads, so the first A that seats him and his
channel catch-up (boundary digests) show at least one older torrent and the head count; JOIN §6.4
`after` entries also show the author of an A a lagging author wrote without seating him. Fix:
reword to "he sees k ≥ 1 older announcements as opaque digests; never names, sizes, store ids or
content"; if even that matters, start a new channel epoch (TRANSPORT §9) before a join. Evidence:
plan reading.

**T-m6. The enqueue snapshot is taken before the uploads.** (Breaker 1, attack 9; breaker 2,
attack 4.) The snapshot is at step 2, the uploads at step 3 take up to days and the server can
stretch them, so a member added during uploads is never seated or sent A (Signal's compose-time
semantics, but the server can use it to exclude chosen newcomers), and then sees A as a digest or
as `after`. Fix: take the snapshot after step 3 (the uploads carry no audience); if membership
changed since the dialog, ask the user to confirm the new list. Evidence: plan reading.

**T-m7. A re-share's `sharedFrom` points newcomers at the older A.** (Breaker 2, attack 5.) Field
214 is committed into the new A, so every seated newcomer learns which boundary digest is the
source torrent, and from a subset re-share that the source held more. Fix: leave out `sharedFrom`
for bt; keep the source only as local metadata on the sharer's device. Evidence: plan §6.6.

**T-m8. Blame goes to the wrong person for a relayed A.** (Breaker 2, attack 6.) §6.2 and §7 blame
A's author for BAD_PIECE or a malformed torrent, but for an A that X forged in Y's name and relayed,
X chose everything. Fix: blame the account that delivered A (live sender, or the relayer by
provenance); show "author unconfirmed" until `CLASSIFY` reports `confirmedByAuthor`. Evidence: plan
reading.

**T-m9. Responders have no request caps.** (Breaker 2, attack 7.) The 32 MiB limit is enforced
only by the requester: a seated member can ask for all 4096 pieces in one request (one `SERVE`
building up to 256 GiB, about 610 MB of memory per 64 MiB piece), or repeat 32 MiB requests to every
seeder (about 200 B in, 32 MiB uploaded, roughly 10^5x), exhausting their upload quota so their
ordinary attachments fail. Automatic in the private profile, attributable to him. Fix: the
responder enforces at most 32 MiB per request, a byte budget per requester and torrent per day
(for example 2×L), refuses a repeat of the same piece to the same requester within the CDN
lifetime, and queues requests (see T-M3). Evidence: the judge's memory measurement
(`/tmp/zrdt-apps-btjudge/core/Bench/Main.lean`); plan §6.3.

**T-m10. A copied nonce collides store ids.** (Breaker 2, attack 8.) The store id is
SHA-256("zrdtT1" ‖ channel ‖ author ‖ nonce); X forges A1' in Y's name with A1's nonce and relays
it; members still repairing A1 bind A1' first, then A1 fails `OPEN_PIECES`/`BIND_PIECES`, and
responders find the store ambiguously. Denial of service only, attributable to X. Fix: key the
host's piece stores by A's digest, send A's digest with `storeId` in requests, and refuse a second
A with the same (author, nonce) in a channel. Evidence: plan §2.

**T-m11. Responders do not check that the store belongs to the request's group.** (Breaker 2,
attack 9.) §6.3 checks "current member" against the request's `groupId`, then finds the store by
`storeId` alone; a member removed from G2 but still in G1 names G1 with a G2 store id. Limited to
torrents he was sent, so it defeats only the host's defence in depth. Fix: check that the store's
channel is in the request's Signal group and that the requester is a current member of it.
Evidence: plan §6.3.

**T-m12. Requesters have no seat check, so a deliberate leak becomes an automatic fetch.**
(Breaker 2, attack 10.) X relays A1, which does not seat newcomer N, inside a `SERVE` reply; N's
`ACCEPT_VIEW` stores it (it checks only that the opening matches and has an audience), and N's
client offers it, opens it and fetches every piece from A1's pointers without any user action.
Fix: the fork never offers, opens or fetches an A, and never keeps an opening, whose audience does
not seat its own ACI under its own key tag (the JOIN §4.5 import check). Evidence: plan reading;
`Proto.lean` `checkEntry`.

**T-m13. §8.6 omits the recipients ⊆ seats duty for the Content 205 send job.** (Breaker 2,
attack 12; holds only if the new job keeps JOIN's invariant.) "A member added during the freeze is
not sent A" is true only if the send job uses the step-2 snapshot and not `getRecipients()` at step
7. Fix: add "A's recipients ⊆ A's seated audience at every attempt, including job retries and
409/410 re-sends" to §8.6, pinned by the JOIN TypeScript invariant test for the 205 job. Evidence:
plan §8.6.

### Attacks that failed (no change needed)

- Replay, injection and reorder (requests, replies, A envelopes, CDN objects, piece lists,
  `sealedOnCdn`, fake pieces or F): duplicates are dropped (`MessageReceiver.preload.ts:2021`),
  request ids are single-use, the seal's AAD covers the header, pointers carry a committed key and
  digest checked by Desktop (`AttachmentCrypto.node.ts`), a bound store marks anything outside F's
  list IGNORED, and `SERVE` never releases a piece to an unseated account or a swapped key (C4).
  Add a replayed-request test to the B7 harness. (Breaker 1, attack 10.)
- Content-addressed pull or an existence test by a newcomer holding an older file: digests are
  salted by the secret store id; keep deduplication out, or local-only and constant-time. (Breaker
  2, attack 13.)
- A newcomer reaching pieces through repair: he cannot name a piece or store, and `serve_content`
  gives an unseated requester no opening (C4). (Breaker 2, attack 14.)
- Planting fake pieces or an extra F in a bound store through unsolicited entries: rule 4 marks them
  IGNORED, piece commits use the store id as group (WRONG_CHAT), F is bound by A's manifest digest,
  and `NEEDS_OPENING` blocks records without bytes; keep `NEEDS_OPENING` on every accept path.
  (Breaker 2, attack 15.)
- R2 evidence against an author: nothing is signed or MACed; the only link from an upload to an
  account is the server's own log, already listed in §7. (Breaker 2, attack 16.)
- Replaying a sealed reply or its `sealedOnCdn` pointer: sealed to the checked key, and the request
  id must be open on this device. (Breaker 2, attack 17.)
