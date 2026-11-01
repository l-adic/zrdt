# Amendments applied to PLAN.md, APP.md, PLAN_HUMANS.md and RESTORE_PLAN.md

Date: 2026-11-01. Status: approved by the user (decisions 1–10 in `REVIEW.md` §7, the Mac mini
decision in `REVIEW.md` §0a, and the reconciliation in `UPDATE-690ae65.md`). This file is the
single source of names and decisions for the four documents. Every change it causes in them is
marked **[amendment]** there.

Settled after the rewrite, on review of the four rewritten documents:
- the opening is exactly the committed bytes (A4);
- `message.zrdt` is erasable (A4);
- every later message carries the full disown list, and the `CLASSIFY` precedence is fixed (A8);
- structure-only relays are accepted (A8);
- the advertised theorems are named `Zrdt.CheckedStore.*`, stated in `Crdt/Merkle/Api.lean`
  (A5).

**What it keeps from the teammate's rewrite (690ae65):**
- `CheckedStore` with constructors only;
- `open`/`salvage` as one worklist;
- the chat id inside the hash;
- 1:1-first resend routing and `ZrdtNotFound`;
- restore from anyone, confirmed by live messages;
- a short list of advertised theorems;
- the three limit examples.

**What it changes** is below. Section references `R§`/`U§` point to `REVIEW.md` and
`UPDATE-690ae65.md`.

---

## A1. Two Lean packages: code without Mathlib, proofs with it (R§1.1, U§4.1)

- **`core/` is its own Lake package, `zrdt-core`** (library `Zrdt`, exe `zrdtd`). It imports only
  `Init` and `Std`. It has no `require`, so the Mac builds it without fetching Mathlib.
- **The root package (`zrdt`)** keeps library `Crdt` (Mathlib) and `require`s `zrdt-core` by path.
- **Rule:** nothing under `core/` imports Mathlib or `Crdt`.
- **Gate:**
  - `lake build` inside `core/` succeeds on a machine with no Mathlib.
  - `nm` on the linked `zrdtd` binary shows no `initialize_mathlib*`/`initialize_Mathlib*` and no
    full `lean_initialize` call. Check the binary, not an archive: Lake links meta-imported
    objects too.
- **Files in `core/Zrdt/`:**
  - `Digest.lean`, `Sha256.lean`, `Record.lean`, `Encode.lean`, `Proto.lean`;
  - `Store.lean`: `RawStore`, `Built`, `CheckedStore`, `accept`, `acceptAll`, `merge`, `open`,
    `salvage`;
  - `Commit.lean`: the protobuf top-level field scan, and `commit`;
  - `Provenance.lean`: `classify`;
  - `Vectors.lean`;
  - `core/Zrdtd/Main.lean`: the stdin/stdout loop.
- **Files in `Crdt/Merkle/`:**
  - `Defs`, `Integrity`, `Chat`: the spec, over `Finset`;
  - `Bridge.lean`: `toSpec`, `hashSpec`, `abs`, and the bridge lemmas from `Built` to the spec;
  - `Refine.lean`: the refinement theorems;
  - `Api.lean`: the advertised corollaries over `CheckedStore` (A5);
  - `EncodeProofs.lean`: `encode_injective`.
- **Theorems about `Zrdt` definitions live in `Crdt`.** That is still "proofs about the code".

## A2. SHA-256 in pure Lean (R§1.5)

- `Zrdt/Sha256.lean`, about 70 lines, with NIST vectors as `#guard`. There is no `@[extern]`, no
  `opaque` and no C.
- `hashRecord r := sha256 (encode r)` is computable. It runs under `#eval`, and under
  `decide +kernel` for small examples.
- Delete `ffi/sha256.c` and the "vendored SHA-256" wording everywhere.
- A prototype from the review exists, kept outside the repo (`~/devel/zrdt-review-spikes` on the reviewer's machine).

## A3. `zrdtd`, a separate process, replaces the in-process N-API module (R§1.2–1.4)

- **One dispatcher, `Zrdt.Proto.handle : ByteArray → IO ByteArray`,** over
  `initialize stores : IO.Ref (Std.HashMap ChatKey CheckedStore)`. The table holds
  **`CheckedStore`**, so every handle is checked by its type in the shipped code.
- **`zrdtd` is a `lean_exe` with a Mathlib-free closure.**
  - Frames on stdin/stdout: `u32 BE length ‖ u8 op ‖ body`, with responses in request order.
  - Diagnostics go to stderr.
  - The read loop must read until it has the full frame (short reads).
  - It runs with `LEAN_ABORT_ON_PANIC=1`.
- **Frame ops** (replace the C header in PLAN §3.3; all digest lists in replies are sorted):

| Op | Request | Reply |
|---|---|---|
| `VERSION` | none | protocol version, git hash of the Lean build |
| `NEW` | chat key, group id (32) | `OK` |
| `OPEN` | chat key, group id, blob, or a list of encoded records | `OK` \| `MALFORMED` \| `TOO_LARGE` \| `WRONG_CHAT` \| `COLLISION{digest}` \| `UNVERIFIABLE{unverifiable[], missing[]}` |
| `SALVAGE` | same as `OPEN` | `OK{dropped[], missing[]}` (the store is loaded) \| `MALFORMED` \| `TOO_LARGE` \| `WRONG_CHAT` \| `COLLISION{digest}` |
| `COMMIT` | group id, author (16), nonce (32), DataMessage bytes | commitment (32) |
| `HASH` | record parts | digest (no store needed) |
| `ACCEPT` | chat key, record parts | `ACCEPTED{digest}` \| `MISSING{digests[]}` \| `COLLISION{digest}` \| `WRONG_CHAT` \| `TOO_LARGE` |
| `HEADS` / `HAS` / `GET` | chat key [, digest] | sorted digests / bool / record parts |
| `REACH_SET` | chat key, from[] | sorted digests |
| `MERGE` | chat key, blob | as `OPEN`, then union into the open store; `COLLISION`/`WRONG_CHAT` leave it unchanged |
| `CLASSIFY` | chat key, live facts (see A8) | a status per record (A8) |
| `ENCODE` | chat key | blob |
| `CLOSE` | chat key | `OK` |

- **Host side (in the fork):**
  - `ts/zrdt/ZrdtBackend.std.ts`, an async interface;
  - `ts/zrdt/backends/daemon.node.ts`, which spawns `$ZRDT_DAEMON` from the main-window preload,
    or from the main process via `ipcMain.handle`;
  - `ts/zrdt/backends/stub.node.ts`, the day-1 **TypeScript** stub. It replaces `ffi/zrdt_stub.c`
    and is the independent reimplementation for the differential test.
  - The daemon's `exit` triggers a "zrdt unavailable" banner, and nothing is marked accepted. On
    restart it re-`OPEN`s from the SQL rows.
  - `ZRDT_REQUIRE_LEAN=1` refuses the stub.
  - The backend's kind and version are shown on screen.
- **Optional stretch, macOS only:** an in-process `.node` with `@[export zrdt_l_call]` over the
  same `handle`. It needs about 20 lines of C, copies every output (Electron rejects external
  buffers), and guards every entry with an initialised flag. The shipped Linux `libleanrt.a`
  cannot be linked into a `.node` (local-exec TLS); macOS is very likely fine.
- **Delete:** `@zrdt/native` as the primary path, `binding.gyp`, the `mute-state-change`
  template, `libzrdt.a` vendoring, `ffi/zrdt.h`/`ffi/smoke.c` as gates, and the "Electron native
  module ABI" risk row.

## A4. The record: chat id, salted commitment, links, author (R§2.4, R§2.8, U§4.5)

- **Record:** `"zrdt2" ‖ group(32) ‖ commit(32) ‖ u32 nlinks ‖ links (strictly sorted, no
  duplicates, 32 each) ‖ author(16)`.
  - Every field has a fixed size except one array of fixed-size elements, so
    **`encode_injective : Function.Injective encode` holds with no size bound**.
  - The author is the sender's ACI. Links are a canonical type, a strictly sorted array of
    distinct digests built by the single record constructor. Decoding rejects non-canonical
    records.
- **Commitment:** `commit = SHA-256("zrdtP1" ‖ group ‖ author ‖ nonce(32) ‖ DataMessage wire bytes
  with top-level fields 15 (groupV2, which contains the group master key) and 200 (zrdt)
  removed)`.
  - It is computed in Lean (`COMMIT`). The host never hashes.
  - The timestamp and everything the user sees (body, quote, mentions, attachments, previews,
    stickers) are inside it.
  - The nonce is 32 random bytes per message, carried in `ZrdtMeta.nonce`.
- **Store blob:** `"zrdtS2" ‖ group(32) ‖ u32 count ‖ (u32 len ‖ record)*`, sorted by digest.
  - Limits: count < 2^24 and nlinks ≤ 4096.
  - `Built` includes these bounds. `accept` and `open` return `TOO_LARGE` beyond them.
  - The decoder never pre-sizes an allocation from an untrusted count. Add a fuzz vector.
- **The store holds structure only.** The content (the opening: the nonce plus exactly the
  committed bytes, i.e. the DataMessage with fields 15 and 200 already removed) lives in Desktop,
  as a new message attribute `zrdtOpening` marked `erase` in `messageAttributesEraseBehavior`.
  Desktop's delete, expiry and view-once paths remove it. No opening (stored, relayed or dumped)
  carries the group master key; the host supplies the group context from the conversation when it
  re-enters an opening. The frozen send copy `message.zrdt` (A7) is classified `erase` too.

## A5. `CheckedStore` and the advertised statements (U§4.1, U§4.2, U§5)

- **In `Zrdt/Store.lean`, without Mathlib:**
  - **`RawStore` is public** (group, map, head cache). The encapsulation is the daemon boundary.
  - **The map is `Std.ExtTreeMap Digest Rec compare`, and the head cache is
    `Std.ExtTreeSet Digest compare`.** These are extensional, so `=` compares contents, and they
    keep keys sorted. Fallback: `Std.HashMap` with `Equiv`-form statements.
  - **`structure Built`:**
    - every key is its record's hash;
    - every record has the store's group;
    - the head cache equals the keys no record links;
    - there is an accept-order witness (newest first) whose members are exactly the map's values;
    - the size bounds of A4 hold.

    Closure (every link is a key) follows.
  - `CheckedStore := { raw : RawStore, built : Built raw }`.
  - Constructors: `empty`, and `accept` with `rawAccept_built`; a prototype exists in
    the review (kept outside the repo (`~/devel/zrdt-review-spikes` on the reviewer's machine)).
  - **One worklist, `acceptAll : CheckedStore → Array Rec → CheckedStore × Array Rec`,** which
    inserts only through the checked `accept`. `merge`, `open` and `salvage` are defined from it,
    so `Built` holds by construction. A bug in the worklist can only reject records or leave
    leftovers.
- **`Digest`** is a 32-byte ByteArray with `deriving DecidableEq`. Its order compares
  `bytes.data.toList` lexicographically, with `Std.TransOrd` and `Std.LawfulEqOrd`, Mathlib-free.
  `Crdt` lifts it to `LinearOrder`.
- **In `Crdt/Merkle/Bridge.lean`:**
  - `toSpec : Rec → Record Payload Digest Aci`, with `Payload = (group, commit)` and links as a
    `Finset`;
  - `hashSpec`, with `hashSpec (toSpec r) = hashRecord r`;
  - `abs c : Store`;
  - a bridge from `Built` to `AcceptBuilt hashSpec (abs c)`, to the heads cache being right, and
    to there being no collision.
- **Advertised in `Crdt/Merkle/Api.lean`** (pinned by the axiom gate and the README; the `Store`
  theorems are their proofs):

```lean
theorem CheckedStore.fetched (c) : Fetched hashSpec (abs c) (heads hashSpec (abs c))   -- no collision disjunct
theorem CheckedStore.no_collision (c) : ¬ CollisionIn hashSpec (abs c)
theorem CheckedStore.agree (c d) (h : c.heads = d.heads) :                             -- ExtTreeSet: `=` is by content
    abs c = abs d ∨ CollisionIn hashSpec (abs c ∪ abs d)
theorem CheckedStore.abs_accept   -- per result: accepted ⇒ abs c' = accept hashSpec (abs c) (toSpec r) ∧ digest = hashRecord r; missing/collision/wrongChat/tooLarge ⇒ c' = c ∧ (the reason holds)
theorem CheckedStore.abs_merge (h : c.merge d = .ok e) : abs e = abs c ∪ abs d
theorem CheckedStore.open_iff : open g b = .ok c ↔
    ∃ u, decodeBlob b = some (g, u) ∧ WellSized u ∧ AcceptBuilt hashSpec (u.map toSpec) ∧
      ¬ CollisionIn hashSpec (u.map toSpec) ∧ (∀ r ∈ u, r.group = g) ∧ abs c = u.map toSpec ∧ c.group = g
theorem CheckedStore.salvage_spec : salvage g b = .ok (c, dropped) → (same hypotheses on u) →
    abs c = buildRetry hashSpec (u.map toSpec) ∧ dropped = digests of the rest
theorem CheckedStore.encode_open (c) : open c.group (encode c) = .ok c                 -- exact: extensional maps
theorem CheckedStore.confirmed (c d) (hs) (hc : hs ⊆ c.keys) (hd : hs ⊆ d.keys) :      -- "held by the sender"
    c.reachSet hs = d.reachSet hs ∨ CollisionIn hashSpec (abs c ∪ abs d)
theorem CheckedStore.classify_spec   -- CLASSIFY computes the spec's provenance status (A8)
theorem encode_injective : Function.Injective encode
```

- **Spec theorems in `Chat.lean`** are proof obligations, not advertised: `fetched_agree`,
  `fetched_build`, `fetched_union`, `acceptBuilt_union`, `salvage_built`, `salvage_maximal`,
  `confirmed_exact`, `reach_implies_held`, `authorConfirmed_sound` (A8).
  - `fetched_union`, `acceptBuilt_union` and `salvage_maximal` are true as stated, even with
    collisions (verified). The fuel `u.card` for `buildRetry` is exactly tight.
  - Make `closed_build` public (it is `private` at `Defs.lean:259`).
- **Limit examples** (`decide`, over a toy hash):
  1. `withheld_tail_undetectable`;
  2. `tail_replaced_passes_open`;
  3. `gap_indistinguishable`;
  4. **new:** `relay_attribution_indistinguishable`. Without disown, "Alice wrote F and the
     server dropped it" and "Mallory forged F" give a third member identical views.

## A6. Signal wire format (R§2.3, R§2.4)

```proto
message ZrdtMeta {
  repeated bytes links   = 1;   // 32-byte digests: the sender's heads at send time
  optional bytes nonce   = 2;   // 32 bytes, the commitment salt
  optional uint32 version = 3;
  repeated bytes disown  = 4;   // digests of records in the sender's name it did not create (A8)
}
message DataMessage { ... optional ZrdtMeta zrdt = 200; }   // present ⇒ record, if in scope (A7)

message ZrdtResendRequest { bytes groupId = 1; repeated bytes digests = 2; }
message ZrdtResend        { bytes groupId = 1; bytes record = 2; optional bytes opening = 3; } // opening = nonce ‖ DataMessage bytes without fields 15 and 200
message ZrdtNotFound      { bytes groupId = 1; repeated bytes digests = 2; }
message Content { oneof content { ...; ZrdtResendRequest zrdtResendRequest = 200;
                                       ZrdtResend zrdtResend = 201; ZrdtNotFound zrdtNotFound = 202; } }
```

- **Why a sub-message:** an optional sub-message is emitted even when empty. An empty
  `repeated bytes` is invisible on the wire, so a first message could not be told apart from a
  stock one.
- **Why inside the `oneof`:** it matches `MessageReceiver`'s dispatch, and avoids new required
  keys on about 32 `Content` literals.
- **Stock clients** log "Unsupported content message" at error level and drop it. Nothing is
  rendered.

## A7. Scope, hooks, storage, timeline (R§2.2–R§2.7, R§2.9)

- **Scope predicate,** shared by send and receive. A record is a GroupV2 DataMessage from the
  `NormalMessage` job with no `storyContext`, no `reaction` and no `editedMessageTimestamp`.
  - Not covered: edits, deletes, reactions, polls, pins, timer, profile and group changes.
  - 1:1 chats and Note-to-self are out.
  - **Membership changes after zrdt genesis are a non-goal** for live verification. The demo group
    is static: Dave is a member from creation.
- **Send hook:** inside `conversation.queueJob` in
  `ts/jobs/helpers/sendNormalMessage.preload.ts`, after attachments are uploaded. **Freeze once:**
  1. links = `HEADS`;
  2. generate a nonce;
  3. build the Content bytes with `ZrdtMeta`;
  4. `COMMIT`, then `ACCEPT`;
  5. persist `message.zrdt = {links, nonce, digest, contentBytes}` first and the store row second;
  6. send the frozen bytes on every attempt;
  7. at startup, re-accept outgoing messages whose digest is missing.

  Extend `getAttrsFromGroupOptions`. `send.preload.ts` is **not** the hook: it only awaits a send
  that has already started.
- **Receive hook:** in `ts/textsecure/MessageReceiver.preload.ts`.
  - Take the plaintext DataMessage bytes (for sync transcripts, `SyncMessage.sent.message`).
  - Add dispatch for Content 200–202.
  - Accept after the membership check and **before** the local-policy drops.
  - Provenance is `live` when the envelope's sender ACI equals the record's author.
  - Re-enter Desktop only at `handleDataMessage`, through the scope predicate.
- **Persistence:** dedicated SQL tables via a migration.
  - `zrdt_records(conversationId, digest, record)`: append-only, structure only.
  - `zrdt_pending(conversationId, digest, record, messageId)`.
  - `zrdt_provenance(conversationId, digest, kind, byAci, disownedBy)`.
  - **Not `items`:** `Uint8Array` values are JSON-stringified and corrupted on reload. Also,
    `window.storage` does not exist; it is `itemStorage`, with closed typed keys.
  - **Desktop does not keep DataMessage bytes.** It strips them before every DB write and never
    keeps them for received messages. The opening lives in `zrdtOpening` (A4).
- **Timeline:** a new `zrdt-gap` message type takes the referencing message's `received_at`,
  with `sent_at − 1`. The referencing message is restamped. Recovered records are saved with the
  gap's `received_at`, and the gap row is deleted once it resolves. Do not reuse
  `retryPlaceholders`.
- **Blocking** is a permanent divergence in both directions. Document it.

## A8. Provenance, attribution and resend (U§4.4)

- **Provenance per record (host state, trusted):**
  - `live`: the Signal envelope sender equals the record's author, or this device sent it;
  - `relayed(byAci)`;
  - `imported`.
- **`authorConfirmed r`** ⇔ some `live` record from `r.author` reaches r, and no `live` record
  from `r.author` lists r in `disown`.
- **Spec theorem `authorConfirmed_sound`:** if an author's client is honest (it disowns every
  accepted record in its own name that it did not create), then every author-confirmed record
  attributed to it was created by it, or two records collide.
- **`CLASSIFY` (Lean, with `classify_spec`)** returns, per record:
  - `confirmedByAuthor`;
  - `heldBy(aci)`: reached by a live record of another member;
  - `unconfirmed`;
  - `notConfirmedByAuthor`: a live record from the author lists it in `disown`, or the author has
    a live record concurrent with it (neither reaches the other) and no live record from the
    author reaches it. Decided by reachability, never by receive order, so the server cannot cause
    false accusations by reordering. Precedence when several apply: `confirmedByAuthor`,
    `notConfirmedByAuthor`, `heldBy`, `unconfirmed` (a disowned record can never be
    `confirmedByAuthor`).
- **Never refuse a record in your own name.** Refusing would stall everything that links it.
  Accept it, alarm locally ("someone linked a message in your name you did not send"), and add it
  to your disown set. **Every** later message carries the full set in `ZrdtMeta.disown`, because
  only live messages count and the server can drop any single one. Openings contain no field 200,
  so relayed or imported messages never contribute a disown list.
- **Resend:** the request goes 1:1 to the referencing sender first, then to the group. Replies
  are always 1:1.
  - **Relay:** the responder sends `ZrdtResend{record, opening}`. The receiver checks
    `HASH(record parts) == digest` and `COMMIT(opening) == record.commit`, then shows the message
    as "relayed by X", which becomes normal once author-confirmed. A relay **without** an opening
    (the responder no longer holds the content, or the requester joined later) is accepted as
    structure only: it resolves the links and shows "a message from A (content unavailable)".
  - **Author fast path:** once the record arrives, the receiver knows its author. It asks the
    author 1:1, and the author re-sends the original through Desktop's sendLog/`SavedProto` path
    (`handleRetry.preload.ts:236-245`). That copy arrives `live`, so it is author-confirmed at
    once.
  - **Limits of the fast path:** the sendLog serves only within 24 h. It is pruned per recipient
    on delivery receipts, but a victim who never acknowledged keeps its entry.
  - **Relayed messages never apply side-effect fields.** `handleDataMessage.preload.ts:687-711`
    sets the sender's `profileKey` for group messages; a relay must not. The same goes for expire
    timer, group changes and anything outside the scope predicate.
  - If the author's live copy arrives later, it **upgrades** the provenance of the same digest.
    It is never silently dropped by the `(sent_at, sourceServiceId)` dedupe when the digests
    differ.
- **`ZrdtNotFound` is not decisive.**
  - The server can drop the request or the reply.
  - An honest member may lack the record: another of their devices linked it, or the store was
    salvaged, relinked or erased.
  - A not-found from a member for a digest they linked is evidence of inconsistency, not of
    malice.
- **"Seen by"** (renamed "confirmed by"), the **fork marker** and **"A's latest"** use `live`
  records only.
  - The fork marker is defined on `(author, sent_at)` with different digests.
  - Both are cut from the demo acceptance criteria. They stay as optional UI.
- **Remove these claims:** "verified by hash, so it can come from anyone", "Signal's signatures
  check it" (for relayed records), and "confirmation by live links does the job without
  signatures".

## A9. Restore and privacy (U§4.5)

- **Dump = store blob (structure) + a content section keyed by digest** (openings).
  - The exporter leaves out content for `expireTimer > 0`, deleted-for-everyone and view-once.
    The importer refuses such entries.
  - Anyone who joined after a record was sent gets a **structure-only** dump. That resolves their
    links without pre-join content, and replaces "newcomer pending forever".
  - Export requires OS authentication and a "do not share" warning, as Signal's own export does.
  - There is no "mirror" or "server" transport unless the dump is encrypted.
  - Content checks: `COMMIT(opening) == record.commit`.
- **Imported and salvaged records start `imported`.** Unconfirmed imported records are shown in a
  collapsed section without avatars or live links, never inline under a member's name.
- **Say plainly:**
  - the dump leaves Signal's encryption;
  - the DAG metadata (authors, causal shape, count) of expired messages persists;
  - stock link-and-sync and Signal backups carry no zrdt data. A device restored that way has a
    full timeline and an empty store, and how rows are matched is out of scope.
- **The guarantee in plain words:** stage 2 holds against the server, and against a dump-giver who
  sends no live messages. A member who gives a dump and also links fakes live is caught only by
  disown (A8).

## A10. What `open` catches (U§4.3)

- **`open` catches:**
  - removing or altering a record that something links;
  - a link to nothing;
  - a changed group;
  - malformed bytes.
- **`open` does not catch:**
  - removing the newest record (a head);
  - editing a head;
  - appending a forged record.
- **Fix every place that says otherwise:** PLAN §3 ("`zrdt_check` on reload catches it"), PLAN §8
  Beat 4 ("one byte changed"), APP Beat 4, PLAN_HUMANS §2, RESTORE §2 ("any altered record").
- **Stale names to fix:** `zrdt_check`/`check`, `zrdt_reaches`, `accept_rejects_names_missing`,
  `latest_reaches_all_own`, and "`gap_indistinguishable` stated in RESTORE §2".

## A11. Villain, harness, demo (R§3, U§4.6)

- **Pin Signal-Desktop `v8.33.0`** (`be0ed1340b9798323d59129b43504062d235e23d`), with Electron
  44.9.1, Node 24.22.0 and pnpm 11.24.0 (`npm i -g pnpm@11.24.0`).
- **The fork is built and run on the Mac mini** (darwin-arm64). `zrdtd` is built there too, with
  the darwin Lean toolchain; nothing can be cross-built. The Linux box keeps the Lean proof work.
- **EvilServer** overrides `handleMessage` (for `deviceId ≠ 1`) plus `prepareMultiDeviceMessage`,
  **not `send()`**.
  - **Rules:**
    - `dropGroupMsg(from, to)` once, matching recipients ≥ 2 and the inferred sender;
    - `blackhole(to)`, which discards;
    - `hold(to)` / `release(to)`.

    Arm rules only after a warm-up send. Drop `replay` (Signal already discards replays) and
    `reorder`.
  - **The server can infer the sender** from the recipient set (the group minus the sender) and
    from the sender's own authenticated `SyncMessage.Sent` with the same timestamp. Fix the
    sealed-sender risk row.
  - The mock holds every key, so "real server power" is a policy the rules follow.
- **Harness (`demo/launch.ts`, about 300–400 lines, phase E 1.5–2 days):**
  - `ciMode: 'full'` is required (`link()` needs `window.SignalCI`). Note that its retry unit is
    10× shorter, so set explicit demo timeouts.
  - **Four** Bootstraps (Alice, Bob, Carol, Dave) with `contactCount: 0`, a `phoneName` patch, and
    the group plus the other members in **every** phone's storage state.
  - Link the desktops one after another, then tile the windows. Each desktop sends one warm-up
    message.
  - Dave's desktop is linked just before beat 5.
  - To restart, use `app.close(); app.start()`, **never** `bootstrap.startApp()`, which wipes the
    profile on a failed start.
  - Day-1 H3 spike: desktops exchange sender-key group messages through the mock.
- **Compare code:** "Copy compare code" / "Paste compare code" carries the full sorted heads set.
  On one machine the clipboard is shared. Words are only an "equal?" fingerprint, ≥ 12 words
  (128 bits). **No QR scanning;** Desktop cannot decode QR.
- **Beats** (total ≤ 4 min, leaving time for the intro and the proof pitch within 5 min):
  1. **Codes match (30 s).** Three messages. Copy and paste compare codes: identical.
  2. **Gap (60 s).** `dropGroupMsg(alice, carol)`. Alice sends; Bob sends a *plain* reply. Carol
     sees a gap row above Bob's reply, visible for 3–5 s (`ZRDT_RESEND_DELAY_MS`). The request
     goes to Bob, the message appears in place as "relayed by Bob", and then the author fast path
     makes it "confirmed by Alice".
  3. **Withheld (45 s).** `blackhole(carol)`. Alice sends; nobody replies. Bob copies his compare
     code; Carol pastes it. Carol sees "Bob has 1 message you don't (·k7f2). Asked; no answer."
     Clear the villain; "Ask again" recovers it.
  4. **Doctored restore (40 s).** In Carol's Settings → Internal, export the store. `doctor.ts`
     removes a **linked, non-head** record. Import: `OPEN` fails with "message ·9ac1 is missing"
     (from the `missing` list). "Keep what verifies" loads the rest as `imported`. No on-disk edit:
     the DB is SQLCipher.
  5. **Restore from anyone (60 s, doctored variant only).** Dave imports Bob's export, onto which
     `doctor.ts` automatically appended two fakes attributed to Bob on top of the genuine head.
     Everything is collapsed and grey. Alice writes: the genuine history becomes "held by Alice",
     and Alice's own messages "confirmed". Bob writes: Bob's genuine messages are confirmed, and
     the two fakes are marked "not confirmed by Bob".
- **"A stock client keeps working"** moves to stretch: the mock setup has no stock client.

## A12. Pitch and claims (R§4)

- **Replace "a malicious server cannot drop, reorder, withhold, or rewrite history without
  detection"** (PLAN §1, PLAN_HUMANS intro, APP closing line) with:

  > A server cannot make a member's app accept a history with a hole in it: if any later message
  > builds on one you lack, you are told and it is fetched. Two members can confirm with one code
  > that they hold the same set of messages; once the server splits a group it can never merge it
  > back without the gap showing. The server can still delay, hold back the newest messages until
  > someone replies or members compare, and deliver concurrent messages in different orders.

- **Gaps and "withheld" do not prove server fault.** A member can link a made-up digest, and an
  offline author produces the same result. Word the UI that way.
- **Trusted base:**
  - the Lean compiler and runtime;
  - the frame codec and protobuf field scan, which are Lean but unproved and small;
  - the TS client;
  - host duties: provenance flags, passing the right bytes, the scope predicate, UI wording.

  There is no C and no external SHA-256.
- **Links are receipts visible to the whole group.** Say so.

## A13. Logistics

- **Phase estimates:**
  - A: 1 d;
  - B: 3–4 d (split, certificate, refinement, `Api.lean`);
  - C: `zrdtd`, frame protocol, vectors and the TS-stub differential, 1–1.5 d;
  - D: 5–6 d;
  - E: 1.5–2 d;
  - F: 1–2 d.
- **Gates:**
  - Rung 6 runs `zrdtd` over `vectors.json`.
  - Rung 7 diffs the TS stub against `zrdtd` over the same vectors, on the Mac.
  - Rung 8 is beats 1–5.
  - Add the closure gate from A1.
- **Checkpoints, dated from day 1** (the deadline is still open):
  - **F0, day 1 on the Mac:**
    - `pnpm install` and `generate` at v8.33.0, and `pnpm start` shows the link screen;
    - the `twoClients` mock test passes;
    - the backend shows its kind and version;
    - `zrdtd` completes one `ACCEPT` round trip inside the fork's Electron;
    - `kill -9` on `zrdtd` shows the banner.
  - **F1, day 2:** four desktops in "Camping" exchange messages; `dropGroupMsg` visibly drops one.
  - **F2, day 3, go/no-go:** `demo/smoke.ts` (Playwright) passes: three sends, the same digests
    everywhere, and `MISSING` after a drop. If not green, start the mini-client on day 4 with
    2 days.
  - **F3, day 5:** the relay and author-resend round trip, plus the gap and code UI.
  - **F4, day 6:** the backend is switched to `zrdtd`, and a cold-start rehearsal.
- **For the fallback to reuse work:** the rules are pure `demo/rules.ts` with two adapters, and the
  UI lives in `ts/zrdt/ui` with plain props and no imports from Signal's `ts/`.
- **Linux box:** extend the LV before creating Lean worktrees (18 GB free; a Mathlib checkout
  takes 6.9 GB).
- **Agent access to the Mac:** add this box's SSH key, or run Claude Code on the Mac. Launch
  Signal from the GUI session (Aqua, Keychain).
- **Smaller corrections:**
  - `NODE_APP_INSTANCE` needs `config/local-<name>.json`;
  - `SIGNAL_ENABLE_HTTP` is not a TLS escape hatch;
  - Electron's binary downloads lazily;
  - public-fork CI does not run test-mock.
