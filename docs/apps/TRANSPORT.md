# TRANSPORT: Signal + zrdt as a transport for group apps

Status: design, 2026-11-01. Not implemented. It builds on JOIN_PLAN v2 (branch `join`) and changes
nothing in the demo build. It is the layer under the two apps (git repository sharing, torrent-style
file sharing); their own documents say how each one uses it.

## 0. Summary

**What it is.** Members of a Signal group exchange *app records* the way they exchange chat
messages: each one is a zrdt record (same format, same store, same proofs) whose commitment covers
an app message instead of a chat message. Bulk data travels as Signal attachments (encrypted once,
uploaded once to Signal's CDN, fetched by each member), named inside the commitment by a SHA-256
Merkle root, and checked piece by piece. Every reply that carries content goes through JOIN's one
Lean gate, `SERVE`.

**It is TCP-like** in reliability, retransmission, integrity and completeness. **It is not** an
ordered byte stream (the order is a causal graph), it has no flow or congestion control, it is
store-and-forward, and it has no peer-to-peer path (Signal's WebRTC is for calls only). On Signal's
own servers, bulk data meets rate limits and probably the terms of service; the mock server or a
self-hosted server avoids both (§11).

**The design in seven lines.**
1. A **channel** is one zrdt store per (Signal group, app, name). Its id is a hash of the three, and
   it sits in the record's `group` field. The record format, the store and the advertised theorems
   do not change.
2. An **app message** is a new `Content` field 205, laid out like a `DataMessage`, so `COMMIT` works
   as is. Its committed bytes hold the audience (field 201, as JOIN), the app tag and channel name,
   the app's payload, and **blob references** (BEP 52 root and length).
3. A **blob** travels in **pieces**, one Signal attachment each. A **carrier** (Signal's
   `AttachmentPointer` plus the piece's Merkle proof) sits outside the commitment. Lean checks each
   piece against the committed root.
4. **Carriers are content.** A CDN pointer is a bearer token, so a carrier goes only in the live
   message (to the audience) or in a sealed `SERVE` reply to a seated requester. A member serves
   pieces of a record only if it got them *through that record* (the **via rule**), so naming a
   known root pulls nothing old.
5. **Retransmission** has three paths: gap repair (JOIN's per-digest `SERVE`), Signal's own retry
   (24 h), and a new re-upload request. All are 1:1, gated by `SERVE`, and sealed.
6. **The guarantees** come from the existing theorems (complete structure, causal order,
   convergence, audience-gated content), plus three new Lean pieces: the app header check, the
   piece check, and `SERVE`'s blob entries.
7. **No signatures.** Authorship comes from Signal's deniable channels, as for chat today.

## 1. What carries over, what generalizes

| Chat today (JOIN v2) | For apps | Change |
|---|---|---|
| Record `zrdt2`: group ‖ commit ‖ links ‖ author | the same | `group` holds a channel id |
| One store per Signal group | one store per channel (§2) | a store kind; `CHANNEL`, `NEW_CHANNEL` |
| Commitment over the `DataMessage` minus fields 15 and 200 | over the app message minus 15 and 200 (§3) | none to `COMMIT` |
| Audience in field 201, `AUDIENCE`, `seats` | the same field and rules | none |
| Scope predicate (A7) | `appHeader` (Lean), plus each app's choice of what to publish (§3.2) | new |
| Attachments in the `DataMessage`: shown, auto-downloaded | blobs: roots committed, carriers outside the commitment (§4) | new |
| `SERVE` gates openings | it gates openings, `have` entries and `carrier` entries (§5.3) | extended |
| Seal, solicited replies, `ACCEPT_VIEW` (JOIN §4.3, §4.4) | the same | none |
| Relative store for newcomers (JOIN §6) | the same, per channel | none |
| Provenance, disown, `CLASSIFY` (A8) | the same, per channel | none |

## 2. Channels

- **Id.** `channelId = SHA-256("zrdtC1" ‖ group (32) ‖ u8 len ‖ app ‖ u8 len ‖ name)`. `app` and
  `name` are 1 to 64 bytes of UTF-8. Lean `App.channelId`, op `CHANNEL`; the host never hashes (A4).
- **Store.** A channel store is a zrdt store whose `group` is the channel id. It also keeps its
  (Signal group, app, name): the store blob `zrdtS4` is `zrdtS3` plus these three. `NEW_CHANNEL`
  opens a closed one; a device with no store opens a relative one and catches up (JOIN §6.1).
- **Why a separate store.** A bulk app never stalls the chat (otherwise a missing app record would
  make chat records wait). Compare codes are per channel. A channel can be retired as a whole
  (§9). The chat store and its proofs stay as they are.
- **Audience: one per channel.** Every record of a channel is addressed to the Signal group's
  members, computed as JOIN §3.2 does at enqueue and freeze. There are no smaller audiences inside a
  channel. Reason: a member not seated in a record that later records link can never resolve it (a
  closed store takes no boundary digests, JOIN §6.2), so the channel would split for him. To
  publish to fewer people, use a Signal group with fewer people. Signal groups are the audience
  mechanism (R3).
- **Discovery.** A member learns of a channel from a record that seats it. A catch-up names only
  the channels in which the requester is seated in some record; otherwise the channel's name and
  existence would leak.
- **Apps.** A client opens channels only for apps it runs and ignores the rest. App tags are short
  ASCII strings listed in `core/Zrdt/App.lean` (`git`, `bt`).
- **Cap.** 256 members (JOIN §12.2). Over it, apps have no stock fallback: `publish` fails.

## 3. The app message

### 3.1 Layout

```proto
message ZrdtAppMessage {                   // Content field 205; laid out like a DataMessage
  optional GroupContextV2 groupV2 = 15;    // routing; not committed (as in chat)
  optional ZrdtMeta zrdt = 200;            // links, nonce, version, disown, carriers; not committed
  optional bytes zrdtAudience = 201;       // committed, required (JOIN_PLAN §3.2)
  optional string app = 210;               // committed: the app tag, "git" or "bt"
  optional string channel = 211;           // committed: the channel name within the app
  optional bytes body = 212;               // committed: the app's payload, at most 32 KiB
  repeated bytes blob = 213;               // committed: at most 64 BlobRefs (§4.1), in order
  optional bytes sharedFrom = 214;         // committed: the record this one re-shares (§5.6)
}
```

- **The commitment.** The committed bytes are the message minus fields 15 and 200, by the existing
  `committedBytes`. So the commitment covers the audience, app, channel, body, blob references and
  `sharedFrom`. This is the "app payload commitment": nothing new is hashed.
- **A strict schema.** `appHeader o` (Lean) accepts an opening only if its committed bytes hold
  exactly one field 201, 210 and 211, at most one 212 and 214, at most 64 fields 213 of 41 bytes
  each, and no other field. So an app opening is never a chat message (it has no field 1 or 7),
  and never ephemeral (it has no field 5 or 14, so `ephemeral` is false: `appOpening_lasting`).
- **Accept.** On a channel store, `ACCEPT`, `ACCEPT_RECORD` and `ACCEPT_VIEW` require `appHeader o`
  to name the store's app and channel (`BAD_APP` otherwise), on top of JOIN's `BAD_OPENING` and
  `NO_AUDIENCE`. The commitment hashes `group`, which here is the channel id, so an opening cannot
  move between channels, or between chat and an app.

### 3.2 Scope predicates

- **Transport level** (one function for send and receive): a `Content.zrdtApp` whose `groupV2`
  names a group the receiver is a member of, whose opening passes `appHeader`, for an app the
  receiver runs. The chat predicate (A7) is unchanged and never matches Content 205.
- **App level:** each app decides which of its events are records. A record is for something that
  must persist, converge and be compared: a git push, a ref update, a shared torrent. Transfers,
  progress, availability and requests are never records. They are `SERVE` requests and replies
  (§5.4). Rule of thumb: **records announce, frames transfer.** This keeps stores small (§9).

### 3.3 Signal's mechanisms it reuses

- **Sender keys.** `sendContentMessageToGroup` takes any `Content`
  (`ts/util/sendToGroup.preload.ts:177`), so Content 205 goes to the group in one sender-key
  message, sealed sender v2, as chat does.
- **Stock clients.** A phone decrypts Content 205, logs it and drops it (Desktop
  `MessageReceiver.preload.ts:2612-2672`, Android "Got unrecognized message!"). It never fetches a
  blob. Members on stock clients only take no part in apps.
- **Own devices.** A stock sync transcript carries only a `DataMessage`. So the fork also sends the
  Content 1:1 to its own account's other devices. There it counts as `live` (own account), as a sync
  transcript does (A8).
- **Signal's retry.** The fork sends Content 205 with a send type that `shouldSaveProto` keeps
  (`ts/util/handleMessageSend.preload.ts:93`). A member that fails to decrypt then gets Signal's
  own re-send within 24 h. This is stock, with Signal's own 24 h exposure (JOIN §4.3); zrdt never
  triggers it.

## 4. Blobs, pieces and carriers

### 4.1 Blob references (committed)

- **BlobRef** (41 bytes): root (32) ‖ length (u64, at least 1) ‖ kind (u8: 0 data, 1 index).
- **Root:** the BEP 52 "pieces root". Each 16 KiB leaf (the last may be shorter) is hashed with
  SHA-256, the leaf list is padded with 32 zero bytes to a power of two, and pairs are hashed up to
  one digest. Checked here: a re-implementation of the BEP 52 reference creator
  (`/tmp/zrdt-apps-transport/scripts/bep52_check.py`, 11 sizes, 6 piece lengths) shows that **the root
  does not depend on the piece length**. So a blob's name depends only on its bytes. The piece
  length is a transfer choice and is not committed. A torrent's file roots are these roots.
- **Index blobs:** the bytes of a kind-1 blob are up to 2^20 BlobRefs of kind 0. They count as
  blobs of the same record (a torrent with many files). Depth is 1.
- Equal bytes give equal roots, so anyone holding a candidate file can test a root. Roots therefore
  stay inside openings (content) and carrier proofs (content, §4.3). They never appear in boundary
  digests, logs or plaintext metadata.

### 4.2 Pieces

- A **piece** is 2^j consecutive leaves starting at a multiple of 2^j, with j from 0 to 12 (16 KiB
  to 64 MiB). The last piece may be short. **One piece is one attachment.** The default is 4 MiB
  (j = 8).
- Why 64 MiB at most: Desktop compares the *padded ciphertext* against the 100 MiB default cap. The
  largest plaintext that fits is 97.49 MiB (fact check A, `AttachmentSize.std.ts:105-118`).
- A **proof** is the list of sibling hashes from the piece's subtree up to the root: (tree depth − j)
  digests, at most 40 for 2^40 leaves.
- **Check.** `CHECK_PIECE(root, length, firstLeaf, j, proof, bytes)` returns `OK` or `BAD_PIECE`.
  Signal checks the MAC and the ciphertext digest of the whole attachment
  (`AttachmentCrypto.node.ts:476-492`). zrdt checks the plaintext against the commitment. A bad
  piece is blamed on whoever sent its carrier: attributable, but only to the receiver, like a gap
  (A12).
- **Complete.** The app sees a blob only when pieces covering `[0, length)` have all passed
  (`assemble_root`). The fallback, simpler to prove, is to hash the assembled bytes once with
  `BLOB_ROOT` and compare (`blobRoot_bound`). The compiled `zrdtd` hashes at about **45 MiB/s**
  (measured here: `COMMIT` of 16 MiB in 0.35 s), so a 1 GiB blob takes about 25 s.

### 4.3 Carriers (not committed)

```proto
message ZrdtCarrier { uint32 blob = 1;           // index in the record's blobs (index blobs expanded)
                      uint64 firstLeaf = 2;  uint32 log2Leaves = 3;   // the piece
                      repeated bytes proof = 4;                       // sibling hashes, bottom up
                      AttachmentPointer pointer = 5; }                // Signal's own pointer
message ZrdtMeta { /* 1-4 as today */ repeated ZrdtCarrier carriers = 5;
                   optional AttachmentPointer carrierList = 6; }      // when carriers > 16 KiB
```

- **Fresh keys.** Each upload for a record uses a fresh random key and a new CDN object. Desktop's
  own upload path reuses the CDN object and key of the same plaintext for 3 days
  (`ts/util/uploadAttachment.preload.ts:52, 74-91`); the fork's blob uploads skip that reuse. A
  carrier is never reused for another record. Otherwise the server could link the two records
  through the shared object, and a newcomer could receive a token for an older copy.
- **Downloads** use Signal's own code: an unauthenticated GET that resumes from an offset
  (`ts/textsecure/downloadAttachment.preload.ts:161-193`). The fork calls it directly, outside the
  message-attachment pipeline. So nothing shows in the timeline and no automatic download rule runs.
- **Expiry.** CDN copies last about 30 days (`getMessageQueueTime.dom.ts:8-20`). A carrier is a
  hint, kept with its `uploadTimestamp` and dropped after 30 days. The commitment names the bytes,
  never a CDN key.

### 4.4 Two rules: carriers are content, and the via rule

**Carriers go where content goes.** A pointer lets anyone fetch and decrypt the piece until the copy
expires. So a carrier appears only:
- in the live message (field 200, to the Signal recipients, who are inside the audience, JOIN §3.2);
  or
- in a `SERVE` reply, as a `carrier` entry for a record whose opening the same reply releases
  (seated under the checked key) and sealed to that key.

It never goes into an export to another account, a chat message or a log.

**The via rule.** A member releases pieces of root X under record r (as carriers or `have` bits) only
for pieces it obtained *through r*. That means either it wrote r and uploaded the pieces, or it
downloaded them from a carrier delivered for r and they passed `CHECK_PIECE`. The same root in
another record never counts. `via(r)` is host state, a set of (root, leaf ranges) kept like `live`
(A8), and it is passed to `SERVE`.

- *Attack it stops.* Bob joins. He knows the root of a public file the group shared before he joined.
  He publishes a record naming that root (he is seated in it, as its author) and asks for its pieces.
  Without the rule, Alice serves her pre-join copy: Bob gets older data and learns that the group had
  the file. With the rule, only Bob's own upload stands behind his record.
- *Cost.* Transfers are not deduplicated across records: a re-share is uploaded and downloaded
  again. Disk storage can still be shared by root. (Later option: a member that already holds the
  bytes checks the new carrier's ciphertext digest against its own encryption under that carrier's
  key and IV, fetching only the 16-byte IV. A correct digest shows that the uploader had the bytes.)
- *Why per piece.* Suppose a member marked a whole blob "via r" after checking one piece. Then the
  record's author could get the rest from it with only one piece in hand.

## 5. What each party sends, stores and checks

### 5.1 Publishing (the author)

1. The app calls `publish` (§10).
2. For each attachment, `zrdtd` computes the piece roots (`PIECE_ROOT`), then the root and every
   piece's proof (`BLOB_ROOT`). The host uploads each piece with a fresh key, paced (§11).
3. **Freeze** as JOIN §4.1: the audience snapshot at enqueue, keys at freeze, `AUDIENCE`. Then build
   the committed fields, `COMMIT`, take the links from `LINKABLE`, run `ACCEPT` with the opening,
   and persist. Set `via(r)` to every piece.
4. Send Content 205 to the group (sender key), with the carriers in `ZrdtMeta`, or in a
   `carrierList` attachment if they are over 16 KiB. Send it 1:1 to the account's own devices too.
5. **Size check before sending:** the whole Content must be at most 64 KiB. The server refuses
   more than 96 KiB per recipient with 413 (`MessageSender.java:77`), and Desktop treats 413 as a
   rate limit and does not retry (`sendToGroup.preload.ts:982-985`).

### 5.2 Receiving live (each member)

1. Dispatch Content 205. `groupV2` gives the Signal group. Check membership as in A7. `ACCEPT` into
   the channel store. A device with no store for that channel opens a relative one and catches up
   (JOIN §6.1).
2. `MISSING` means the record waits in `zrdt_pending` and gap repair runs (A8, JOIN §4.4).
3. Store the carriers. Fetch them according to the app's policy (eager for small blobs, on demand
   for large ones).
4. For each piece: download it, run `CHECK_PIECE`, and add it to `via(r)`.
5. Pass events to the app in accept order (§10).

### 5.3 What `SERVE` adds

- **`Held` gains** `via` (leaf ranges per root obtained through the record) and `carriers` (pieces
  of this record that the responder has already uploaded, or kept from the live message, less
  than 25 days old).
- **`Query` gains** `leaves`: per wanted record, (root, leaf ranges).
- **`Entry` gains** `have d root ranges` (pieces the responder can release for record d) and
  `carrier d c`. Both are emitted only for a record whose opening the same reply releases
  (`serveOpening`), and only inside `via`. Their shape and gate are the same as an opening's; they
  are separate entries so that `serve_content` keeps its statement.
- **`GRANTS`** (new op) returns what `SERVE` would release for this requester and key, before any
  upload. The host uploads only that.

### 5.4 Repair and re-upload (retransmission)

- **Missing records:** JOIN's per-digest `SERVE`, unchanged.
- **Missing pieces** (a carrier expired with 404 or 403, never came, or failed `CHECK_PIECE`): send
  `ZrdtServeRequest` 1:1 (per-digest `[r]`, `leaves`). Ask the author first, then members whose
  live records reach r (`holders`, A8). Ask at most three at once, on disjoint ranges.
- **Responder:** `GRANTS`, then upload the granted pieces with fresh keys (or reuse a held carrier
  for r), then `SERVE` with those carriers, seal, and send 1:1. A sealed reply over 48 KiB is
  itself uploaded as an attachment, and the 1:1 message carries its pointer. The bytes are sealed
  to the checked key, so that pointer gives nobody else the content.
- **Requester:** the JOIN §4.4 checks (solicited, unsealed, responder key unchanged), then
  `ACCEPT_VIEW`; then download, `CHECK_PIECE`, and add to `via(r)`.
- Availability is never broadcast. A group-wide "have" message would show a newcomer the sizes of
  older blobs. `have` entries come only in sealed replies.

### 5.5 Newcomers (R1)

This is JOIN §6, per channel. A newcomer gets a relative store: the records sent to him, with their
content and carriers; `after` structure; boundary digests for older records. No older blob, carrier,
`have` bit or channel name reaches him. Apps must work from a relative history. For example, the git
app gets a snapshot only if a member shares one, and the torrent app sees torrents shared after he
joined, or shared again.

### 5.6 Sharing by choice

`share(record, to)` publishes a new record with the same body and blobs and `sharedFrom` set. The
sharer uploads it fresh, so by the via rule its own upload is the only source.
- `to` = the channel: every current member, newcomers included.
- `to` = one account: 1:1, outside the store, as JOIN §8.4. The recipient keeps it as "shared",
  not as channel history.

A share happens only from a user action, and the fork shows "you shared … with …". Members who
forward older data on purpose are a non-goal (JOIN §1). The point is that nothing shares
automatically.

## 6. What the transport guarantees, and what it does not

| Guarantee | What it means for an app | From |
|---|---|---|
| Complete structure | A channel store holds exactly what its heads reach. A missing record shows as a gap, with the exact list of missing digests, and is fetched. Same heads, same records. | `CheckedStore.fetched`, `abs_accept`, `agree`, `agree_rel` |
| Complete, verified content | An app sees a record only with an opening that matches it, and a blob only when all its bytes match the committed root. Or SHA-256 has a collision. | `acceptRecord_accepted`, `openingMatches_spec`, `opening_bound`; new `checkPiece_sound`, `assemble_root` (or `blobRoot_bound`) |
| Causal order | Events come in accept order: each record after every record it links. Concurrent records come in any order, which may differ between members. | `abs_accept`, `AcceptBuilt` |
| Convergence | Same records give the same store, whatever the order. App state converges if it is a function of the record set (an app duty). | `abs_merge`, `fetched_union`, `acceptBuilt_union`, `agree` |
| Acknowledgement | A later live record of member M that reaches r shows that M holds r. There is no acknowledgement for blob bytes. | `confirmed`, `reach_implies_held`, `classify_spec` |
| Audience-gated release | Content (opening, carrier, `have`) leaves a member only to an account seated by the record's own committed audience, sealed to the checked key, and never from a copy obtained through another record. | `serve_content`, `serve_content_complete`, `audience_bound`, `run_serve_content`; new `serve_blobs` |
| Deniable authenticity | No signature and no MAC. Live copies are authenticated by Signal. A relayed copy is `relayed(by)` until the author confirms it. | `authorConfirmed_sound`, `classify_spec`; JOIN §7.4, §10a |
| Retransmission | Signal resumes uploads (tus, up to 10 retries) and downloads (from an offset). zrdt repairs records and re-uploads pieces. | Signal; §5.4 |

**Not provided:**
- **An ordered byte stream.** The unit is a record, and the order is a graph.
- **Flow control and congestion control.** A pacer keeps under Signal's limits (§11); nothing adapts
  to the receivers.
- **Latency bounds.** The transport is store-and-forward. The server can delay anything, and can
  hold back the newest record until a later record or a compare code shows it
  (`withheld_tail_undetectable`).
- **Bandwidth beyond Signal's CDN and its limits.** There is no peer-to-peer path.
- **Availability.** CDN copies last about 30 days. After that, a blob exists only where members keep
  it (§9).
- **Hiding traffic from the server.** It sees who uploads what size and when, who downloads which
  object (IP, count), the pattern of 1:1 requests and replies, and the size of group sends. Padding
  (buckets of 1.05^k) and one piece size hide most of each blob's length, not the volume.
- **Bulk use of Signal's own servers** (§11).
- **Delivery to stock clients.**

| TCP | zrdt transport |
|---|---|
| Sequence numbers | Hash links (a graph, not a line) |
| ACK | A later live record that reaches yours; a compare code |
| Retransmission | Per-digest `SERVE`, re-upload request, Signal's retry |
| Checksum | SHA-256 commitment and Merkle root (cryptographic) |
| In-order byte stream | Causal order of records only |
| Flow and congestion control | None; a pacer for Signal's limits |
| Ports and connections | App tag and channel |

## 7. Lean

### 7.1 Unchanged

Why: the spec's `Record α H K` is generic in its payload, and the shipped payload is `(group,
commit)`, an opaque pair (`Bridge.lean`: `Payload := GroupId × Digest`). An app record is a record
with a different commitment, so nothing about records and stores changes; `group` just reads as
"channel". Only three functions look inside committed bytes: the scan (fields 15 and 200),
`audienceOf` (201) and `ephemeral` (5, 14). The app message uses the first two numbers in the same
way and never uses the last two.

**Same statements and same proofs:**
- Advertised (`Crdt/Merkle/Api.lean`): `CheckedStore.fetched`, `CheckedStore.no_collision`,
  `CheckedStore.agree`, `CheckedStore.abs_accept`, `CheckedStore.abs_merge`,
  `CheckedStore.open_iff`, `CheckedStore.salvage_spec`, `CheckedStore.encode_open`,
  `CheckedStore.confirmed`, `CheckedStore.classify_spec`, `Zrdt.encode_injective`, and JOIN's
  `CheckedStore.agree_rel`, `CheckedStore.serve_content`, `CheckedStore.serve_content_complete`.
- Spec: `fetched_agree`, `fetched_of_build` (`Integrity.lean`); `fetched_build`, `fetched_union`,
  `acceptBuilt_union`, `acceptBuilt_insert`, `salvage_built`, `salvage_maximal`, `confirmed_exact`,
  `reach_implies_held`, `authorConfirmed_sound`, and the four limits `withheld_tail_undetectable`,
  `tail_replaced_passes_open`, `gap_indistinguishable`, `relay_attribution_indistinguishable`
  (`Chat.lean`); `served_heads'`, `served_closed'`, `served_tight'`, `served_boundary'`,
  `agree_rel'`, `newcomer_agree'` (`Rel.lean`).
- Running code: `openingMatches_spec`, `committedBytes_idem`, `commitWithOpening_matches`
  (`Commit.lean`); `serve_content`, `serve_content_complete`, `serve_authorCopy`, `serve_strict`,
  `serve_export`, `serveOpening_spec`, `audience_bound` (`Serve.lean`); `acceptRecord_accepted`,
  `accept_accepted`, `run_audience`, `run_addressed`, `commit_openingMatches`, `acceptView_sound`,
  `acceptView_built`, `acceptView_accepted`, `run_acceptView`, `run_linkable`, `run_newRelative`
  (`Proto.lean`); `ChatStore.encode_reopens`, `linkable_sub`; `rawAcceptRel_built`,
  `acceptAll_sound`, `load_ok`, `merge_ok` (`RelStore.lean`).

**Same statements, proofs gain a case:** the theorems that split on `SERVE`'s entry kinds, once
`have` and `carrier` are added: `serve_after`, `serve_boundary`, `serve_abs`, `serve_heads`,
`serve_closed`, `serve_tight` and the lemmas in `ServeAbs.lean`. `run_serve_content` gains the new
entries under the same header and key.

### 7.2 New (Mathlib-free, in `core/`)

- **`core/Zrdt/App.lean`:** `channelId`, `appHeader`, `blobsOf`, `BlobRef`.
  - `opening_bound`: two openings that match one commit are equal, or SHA-256 has a collision.
    The proof is `audience_bound`'s, with the identity in place of `audienceOf`. So the app tag,
    channel, body and blob references are bound by the record, like the audience.
  - `appOpening_lasting`: an opening that passes `appHeader` is not `ephemeral`.
  - `run_accept_app`: on a channel store, `ACCEPT`, `ACCEPT_RECORD` and `ACCEPT_VIEW` store a record
    with an opening only if `openingMatches` holds, the audience is well formed, and `appHeader`
    names the store's app and channel. Otherwise they reply `BAD_APP` and nothing changes.
- **`core/Zrdt/Blob.lean`:** `blobRoot`, `pieceRoot`, `proofOf`, `checkPiece`.
  - `blobRoot_bound`: two blobs of the same length with the same root are equal, or SHA-256 has a
    collision. The length fixes the shape of the tree, so BEP 52's lack of a leaf/node tag does not
    matter.
  - `checkPiece_complete`: the true piece of a blob, with `proofOf`, passes.
  - `checkPiece_sound`: a piece that passes equals that piece of every blob with that root and
    length, or SHA-256 has a collision.
  - `assemble_root`: pieces that cover `[0, length)` and each pass against one root concatenate to
    a blob with that root, or SHA-256 has a collision. The proof is by induction on the tree; it is
    the hardest new proof.
  - Vectors: roots from the BEP 52 reference algorithm (the script above) and from libtorrent's v2
    test torrents.
- **`Serve` extended** (§5.3):
  - `serve_blobs`: every `have` or `carrier` entry for record d comes after an `addressed` entry for
    d in the same reply whose opening is released (so it seats the requester under the checked
    key), and covers only leaf ranges in `held(d).via`.
  - `serve_blobs_complete`: the converse.
  - `grants_spec`: `GRANTS` returns exactly what `SERVE` would release.
- **Later:** `PRUNE`, with `prune_heads` and `prune_closed` taken from `served_heads'` and
  `served_closed'` (§9).
- **Advertise** `serve_blobs` and `assemble_root` (or `blobRoot_bound`) in `Api.lean`, with
  examples. Keep the rest as proof obligations pinned by the axiom gate. Comparator runs only as the
  very last step.

### 7.3 Tests (`#guard` and examples, like JOIN §7.1)

- Bob names the root of Carol's pre-join blob in his own record: Alice's reply has no carrier and
  no `have` for it (the via rule).
- The carriers of Carol's pre-join record never reach Bob, in a catch-up or in a per-digest
  request.
- A requester whose key changed gets no carrier.
- In strict mode only the author's own reply carries carriers.
- A flipped byte fails `CHECK_PIECE`.
- An opening with field 5, an extra field or a second field 210 fails `appHeader`.
- A chat opening is refused by a channel store, and the other way round.
- One example of each new theorem with every hypothesis discharged, and one bad output each one
  rules out.

### 7.4 New host duties (trusted, like `live` and disown in A8)

- **Fill `via(r)` only** from the record's own uploads, or from bytes downloaded through a carrier
  delivered for r that passed `CHECK_PIECE` against the root in r's opening.
- **Uploads:** a fresh key for every upload, never Desktop's reuse cache.
- **Carriers:** send them only on the two paths of §4.4.
- **Bytes to the app:** pass only bytes that passed the checks.
- **Sending:** check sizes before sending, and pace (§11).
- **Receiving:** dispatch Content 205 through the transport scope predicate, and send the 1:1 copy
  to the account's own devices.
- **The socket:** an app sees only its own tag's channels.

`zrdtd` cannot see where bytes came from, so the via rule rests on these duties, as author copies
rest on the host's `live` set.

## 8. Wire and frame ops

```proto
message Content { oneof content { ...; ZrdtServed zrdtServed = 203; ZrdtServeRequest zrdtServeRequest = 204;
                                       ZrdtAppMessage zrdtApp = 205; } }          // §3.1
message ZrdtServeRequest { /* 1-5 as JOIN_PLAN §10.1 */ repeated ZrdtWantLeaves leaves = 6; }
message ZrdtWantLeaves { bytes record = 1; bytes root = 2; uint64 first = 3; uint64 count = 4; }
message ZrdtServed { /* 1-4 as JOIN_PLAN §10.1 */ optional AttachmentPointer sealedOnCdn = 5; }
```

Frame protocol 4 (`zrdtd`): JOIN's protocol 3, plus:

| Op | Name | Request | Reply |
|---|---|---|---|
| `0x17` | `CHANNEL` | group ‖ app (`str`) ‖ name (`str`) | the channel id |
| `0x18` | `NEW_CHANNEL` | chat ‖ group ‖ app ‖ name ‖ relative (`flag`) | `OK`; `CHAT_OPEN` |
| `0x19` | `PIECE_ROOT` | `u8` j ‖ bytes (at most 2^j leaves) | the piece's subtree root |
| `0x1A` | `BLOB_ROOT` | `u64` length ‖ `u8` j ‖ piece roots (`digests`) | root ‖ one proof per piece |
| `0x1B` | `CHECK_PIECE` | root ‖ `u64` length ‖ `u64` firstLeaf ‖ `u8` j ‖ proof (`digests`) ‖ bytes | `OK`; `BAD_PIECE` |
| `0x1C` | `GRANTS` | as `SERVE`'s request, without carriers | per wanted record: (root, leaf ranges) |
| `0x12` | `SERVE` (changed) | held items add via ranges and carriers; the request adds `leaves` | entries add `0x03` have, `0x04` carrier |
| `0x07`, `0x10`, `0x14` | `ACCEPT`, `ACCEPT_RECORD`, `ACCEPT_VIEW` (changed) | as before | adds `BAD_APP` on a channel store |

New statuses: `0x0C` `BAD_APP`, `0x0D` `BAD_PIECE`. The store blob is `zrdtS4` (§2). A piece frame
of 64 MiB fits the u32 frame length; `zrdtd` reads it in 64 KiB chunks (`Main.lean`).

## 9. Retention and compaction

Bulk data makes retention a real question. What grows, and what may go:

| State | Size | May be dropped? |
|---|---|---|
| Records (structure) | 89 B + 32 B per link (`zrdt2`) | No, within a channel: `fetched` and `agree` need them. See the levers below. |
| Audiences | 32 B per member per record | No: kept after content is erased (JOIN §4.2) |
| Openings | up to about 45 KiB | Yes. The record stays, and `SERVE` then sends structure only |
| Blob bytes | bulk | Yes, by policy (`pin`, `cache`, `drop`). Dropping clears `via` |
| Carriers | about 0.5 KiB per piece | After 30 days, always |
| `via` sets | small | With the bytes |

- **Availability is the members' job.** A blob stays fetchable only while a seated member keeps it
  (CDN copies expire). `status` shows how many members last reported holding it.
- **Few records.** "Records announce, frames transfer" means a push or a share is one record. Bulk
  traffic adds nothing to the store.
- **Lever 1: channel epochs** (no new Lean). A member starts channel `name#2`. Its first record's
  body commits the heads of `name#1`. Members who hold those heads check that they equal their own.
  A newcomer cannot check them; they are opaque digests, as R1 wants. Each member archives `name#1`
  when it likes. Agreement does not span epochs except through that commitment. Late records in
  `name#1` stay there; their authors publish them again in `name#2`.
- **Lever 2: pruning, later.** A member may turn its closed store into a relative one by dropping
  the records below the **stable frontier**: the records that a live record of *every* current
  member reaches. By `reach_implies_held`, every current member holds them, so no current member
  will ask for them. Newcomers get boundary digests for them anyway. This is the view `SERVE`
  already builds, so `served_heads'` (heads unchanged, so compare codes still match),
  `served_closed'` and `agree_rel'` cover it. It needs a `PRUNE` op, and a store kind whose boundary
  is self-vouched. That is a change to JOIN's rule that only catch-up makes relative stores.
- **Exports.** An export to one's own account includes the channel stores, openings, audiences,
  `via` sets and, if asked, blob bytes. An export to another account is `SERVE`'s reply (JOIN §4.5),
  without carriers (bearer tokens) and without blob bytes.

## 10. The API for apps

The transport runs inside the fork, which holds the Signal sessions, sender keys and CDN
credentials. Apps (`git-remote-zrdt`, the torrent app) connect over a Unix socket in the fork's data
directory. Each app has its own token and sees only the channels with its own tag. If the fork is
not running, calls fail with "Signal not running".

```
open(group, app, name)                -> Channel       // derives the id; opens or creates the store
publish(audience, body, attachments)  -> RecordRef     // audience = (group, channel); see below
subscribe(channel, from?)             -> events        // records in accept order, from heads `from`
request(channel, missing)             -> RequestId     // record digests, or (record, root, leaf ranges)
share(channel, record, to)            -> RecordRef     // to = the channel, or one account (§5.6)
status(channel)                       -> heads, compare code, gaps, blob availability, pacer budget
retain(channel, record, root?, policy)                 // pin | cache | drop (§9)
```

- **`publish`.** `audience` names the Signal group and channel. The audience is that group's
  members at enqueue and freeze (JOIN §3.2). A smaller audience means a smaller Signal group (§2).
  `body` is at most 32 KiB. `attachments` are files or bytes, at most 64, with index blobs for more.
  Pieces are uploaded before the freeze. If an upload fails for good (413, a challenge), `publish`
  fails and no record exists. It returns after `ACCEPT` and the hand-off to Signal.
- **`subscribe`** delivers, in accept order:
  - `record` (digest, author, provenance, links, body, blob references);
  - `blob` (progress, complete with a file path, bad piece and from whom, unavailable);
  - `gap` (opened, asked whom, closed);
  - `heads` (new heads and compare code).

  Events are kept, and replayed after a restart from `from`.
- **`request`** asks for missing records (per-digest repair) or pieces (re-upload, §5.4) and
  reports who was asked and what came back. It never needs `since`: content follows the audience.
- **`share`** must come from a user action (§5.6).

## 11. Sizes, pacing, where to run

| Limit | Value | Source (fact check A) |
|---|---|---|
| `DataMessage.body` | 2 KiB; stock receivers drop larger | `longAttachment.std.ts:7`; never used by apps |
| One Content, per recipient | 96 KiB on the server; zrdt keeps to 64 KiB | `MessageSender.java:77` |
| App body; carriers inline; sealed reply inline | 32 KiB; 16 KiB; 48 KiB | this design |
| Attachment | 100 MiB padded by default; pieces at most 64 MiB | `AttachmentSize.std.ts:30-44, 105-118` |
| CDN lifetime | about 30 days | `getMessageQueueTime.dom.ts:8-20` |
| Uploads per account | 1 GB burst, then 1 MB/s; 50 forms, then 1 per 1.2 s | `RateLimiters.java:22-23` (defaults) |
| 1:1 bytes per recipient | 128 MiB burst, then 2000 B/s | `RateLimiters.java:52` (defaults) |
| Sender-key group sends | no open-source limit; a private spam filter | `MessageController.java:627-641` |
| `zrdtd` SHA-256 | about 45 MiB/s | measured here |

- **Pacer** (host): token buckets with these defaults, which production may override, values
  unknown. 413 and 429 mean back off (exponential, with jitter, at most 1 h). Never retry a 413 at
  the same size. A 428 challenge stops transfers and shows Desktop's challenge UI. Keep 1:1 frames
  tiny; bulk goes to the CDN.
- **Where to run.**
  - *Signal's own servers:* only small transfers that a person starts. The terms forbid "bulk
    messaging, auto-messaging" and disrupting performance, and a daemon that repairs and
    re-uploads by itself is arguably auto-messaging.
  - *The bundled mock server* is the cheap option for the apps and the demo. It runs on loopback,
    with no limits, and its CDN3 store never expires; attachments are held in memory, so large
    transfers use RAM. The "evil" mock needs one more hook: delete a CDN object, to show re-upload.
  - *A self-hosted Signal-Server* is an infrastructure project: FoundationDB, DynamoDB, Redis, CDNs,
    storage, registration, CDSI and SVR (SGX), key transparency. Desktop also needs a
    `libsignal-net` routing patch or a tunnel to localhost.

## 12. Requirements and threat model

**R1 (no older data for later joiners).** Each row is an attack, and what stops it.
- A catch-up of a channel would return pre-join content. `SERVE` releases an opening only under its
  own committed audience (`serve_content`).
- A relayed CDN pointer works as a bearer token. Carriers go only in live messages and in `SERVE`
  entries under a released opening, sealed (`serve_blobs`).
- A newcomer names a known root to pull older bytes, or to test whether the group had them. The via
  rule stops it (§4.4).
- Desktop's 3-day upload reuse would hand a newcomer a token for an older copy, and would link two
  records for the server. Fresh keys per record stop it (§4.3).
- Group-wide availability messages would show older blob sizes. Availability goes only in sealed
  replies (§5.4).
- A large reply is put on the CDN. Its bytes are sealed to the checked key (§5.4).
- A key swap between the check and the send is stopped by the seal (JOIN §4.3).
- A server-asserted join revision is never read (JOIN H3).
- App duty: a git push whose bundle carries pre-join objects is a share. The git app must detect it
  and ask the user; the transport cannot know.

**R2 (any authenticity must be designated-verifier).**
- Nothing new signs or MACs: blob references, proofs and carriers are hashes and Signal pointers. An
  attachment's MAC uses a key every receiver holds.
- The server authenticates uploaders to itself, as for every Signal attachment. A judge holding the
  server's logs and a member's device could tie an upload to an account; that is Signal's own
  exposure, and re-uploads add more such events (§13).
- What would break R2: requiring signed git commits or tags, keeping sender-key messages, or
  broadcasting per-member tags (JOIN §10a). Apps must not do any of these.

**R3 (reuse Signal first).**
- *Reused:* sender keys for fan-out; pairwise sessions for requests and replies; the CDN
  (encrypt once, upload once, resumable upload and download, MAC and digest checks); Signal's
  retry (sendLog, 24 h); Signal groups as audiences; identity keys for the seal.
- *Added, each for a gap:*
  - re-upload requests: Signal has no backfill between accounts;
  - piece checks: Signal checks only whole files;
  - links and compare codes: Signal gives no transcript consistency;
  - channels and app tags: Signal has no app multiplexing;
  - carrier gating and the via rule: pointers are bearer tokens;
  - the pacer: 413 is treated as a rate limit and never retried.

**Threat model.** The server and the network are the adversary.
- *They can:* drop, delay, hold back the newest record, expire CDN objects early, see sizes, timing,
  IPs and uploaders, swap keys (TOFU), and lie about membership to an author.
- *They cannot:* inject records (Signal authenticates senders), change bytes undetected (MAC and
  Merkle root), read content (end-to-end encryption and the seal), or make an honest member release
  content to an account the author did not seat.

Members are honest or attributable. A member who uploads garbage is caught per piece and named to
the receiver. A member who vouches false boundary digests is named (JOIN §6.2). Closed groups only.

## 13. Limits, risks, staging, effort

**Limits.** No byte stream, no congestion control, no latency bound, no availability after 30 days
without a member's copy, no metadata privacy from the server, no stock-client participation, no
smaller audience within a channel, at most 256 members, no transfer deduplication across records.

**Risks.**
- **Signal behaviour not verified:**
  - stock iOS's handling of an unknown Content field (Desktop and Android drop it silently; for iOS
    only the log line was found);
  - whether a sendLog entry for Content 205 is re-sent correctly;
  - the 1:1 send to one's own devices.
- **Production limits are unknown.** Production overrides the rate limits, and the spam filter is
  private.
- **The fork's upload path must skip Desktop's reuse cache.** Missing it once links records for
  the server.
- **Speed.** At 45 MiB/s, checking large torrents takes minutes. If that is too slow, hash leaves
  on the host and keep only the tree in Lean; the trusted base then grows.
- **`assemble_root` may take longer than planned.** The fallback is `blobRoot_bound` plus one
  re-hash.
- **The mock server keeps attachments in memory,** which limits demo sizes.
- **Relative-store restatements of the advertised theorems are still pending** (JOIN §7.3), and
  they are needed for channels of newcomers.
- **Uploads leave server-side evidence** (R2 above); more relays mean more of it.

**Staging.** These stages depend on JOIN stages 1 to 3: the core of stage 1 is on `join`; the fork's
stages 2 and 3 are not started.
1. **Lean core:** `App.lean`, `Blob.lean`, `zrdtS4`, the ops `CHANNEL` and `NEW_CHANNEL`, the piece
   ops, `BAD_APP`, vectors. Theorems: `opening_bound`, `appOpening_lasting`, `run_accept_app`,
   `blobRoot_bound`, `checkPiece_complete`, `checkPiece_sound`. About 3 to 4 days.
2. **`SERVE` with blobs:** the entries, `GRANTS`, `serve_blobs`, `serve_blobs_complete`,
   `grants_spec`, the extra cases in `ServeAbs`, and `assemble_root`. About 3 days.
3. **The fork:** Content 205 send and receive, uploads with fresh keys, direct downloads, the
   `via` and carrier tables, the pacer, large replies on the CDN, the socket API and events. About
   2 weeks.
4. **The mock harness:** CDN deletion and 413/429 injection. About 2 days.
5. **Later:** epochs (app-level), `PRUNE`, proof of possession by ciphertext digest (to save a
   re-share's download).
