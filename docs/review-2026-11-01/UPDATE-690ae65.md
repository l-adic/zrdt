# Update: how commits 45b9835..690ae65 change the review

Date: 2026-11-01. This compares the teammate's rewrite (plan docs moved to `docs/`; `RESTORE_PLAN.md`;
`CheckedStore`) with `REVIEW.md` and with the decisions taken since. Four verifiers checked the
claims below against the new text, against Lean scratch builds with the pinned v4.35.0 toolchain
(`/tmp/zrdt-diff-*`), and against the Signal clone. Result: 6 confirmed, 11 partly right
(corrected here), 0 refuted.

**Decided by the user so far:**
- the Signal fork is built and run on the Mac mini (`REVIEW.md` §0a);
- Lean is split into a Mathlib-free code library (`Zrdt`) and a proofs library (`Crdt`);
- SHA-256 is pure Lean;
- the review's other recommendations are approved: the `zrdtd` daemon, a salted commitment
  payload, the Signal hook fixes and the demo rewrite.

The rewrite does not reflect any of these yet. PLAN still says N-API, a vendored C `sha256.c`,
`opaque sha256 @[extern]`, and `make lib` building the Mathlib `Crdt` library.

## 1. What the rewrite changed

- **The checked store is a type.** `CheckedStore` = raw hash map + head cache + chat id, plus a
  proof field `Built` (accept-built, chat-bound, cache correct). Only `empty`, `accept`, `merge`,
  `open` and `salvage` can produce one. `zrdt_check` and the raw `zrdt_decode` are gone. `open`
  and `salvage` are one worklist (Kahn's algorithm).
- **The chat id is inside the hashed record.** A record from another chat is rejected
  (`WRONG_CHAT`).
- **The advertised theorems are pruned** to `fetched_agree`, `fetched_build`, `fetched_union`,
  `salvage_maximal` and `confirmed_exact`, plus the refinement and three limit examples.
- **Resend requests** go 1:1 to the member whose message referenced the digest first, and then
  to the group. Replies are always 1:1. A new `ZrdtNotFound` reply exists, and the request
  carries a `groupId`.
- **`RESTORE_PLAN.md`:**
  - A whole-history dump can come from anyone; `open` checks it.
  - Records are "confirmed" once they are reachable from a live message's links.
  - A "foreign marker" flags imported records attributed to a member that member's latest
    message does not reach.
  - A new demo beat 5 has a fourth member (Dave) import a dump.

## 2. Review findings the rewrite resolves

| `REVIEW.md` item | Status |
|---|---|
| §1.6 `decode_encode` stated with `=` on HashMaps | Fixed. `encode_open` is stated through `abs`. It has new defects; see §4.2. |
| §1.6 `abs_accept` unprovable with unchecked decode | Fixed. No unchecked store exists, and the certificate includes `AcceptBuilt`, hence `Closed`. Note `closed_build` is `private` (`Defs.lean:259`) and is missing from phase A's list of things to un-private. |
| §1.7 dead `UNREACHABLE` branch; no UI branch for decode failure | Fixed. `open` has statuses, and `salvage` loads what verifies. |
| Host building payload bytes | Fixed. `zrdt_record` takes the parts and the library builds the bytes. |
| `reaches_iff`; out-of-order arrival into the pending buffer | Fixed: `reachSet_iff` and `salvage_maximal`. `fetched_union`, `acceptBuilt_union` and `salvage_maximal` are **true as stated, even with collisions** (verified). The fuel `u.card` is exactly tight. |
| Resend from another group; n−1 replies to every request | Fixed. The chat id is in the hash, and replies go 1:1. |
| Honesty about limits | Better. `gap_indistinguishable` and the tail-replacement limit are now stated. |

## 3. Still open, unchanged in the new text

Everything in `REVIEW.md` §2–§5 that is not listed above still applies, with section numbers now
under `docs/`:

- **C side:** the Mathlib closure (§1.1); in-process N-API and the Linux runtime problem (§1.2);
  the extern SHA-256 (§1.5).
- **`encode_injective` is still false** with u32 lengths. It becomes true with the commitment
  payload; see §4.2.
- **The `Digest` order** is still not lawful.
- **Payload** is still rebuilt from normalised fields and covers too little of the message.
- **Desktop does not keep the bytes the resend relies on.** APP §4 still says it does.
- **The hooks are still in the wrong places:** send in `send.preload.ts`, receive in
  `handleDataMessage` with no `MessageReceiver` change.
- **Storage:** the blob still goes into `items`/`window.storage`.
- **Timeline:** a recovered message still lands below the reply.
- **Scope:** reactions, edits and deletes are still handled differently on send and receive.
- **Wire format:** `repeated bytes zrdt_links` (an empty list is invisible on the wire); the
  `Content` fields 200–202 sit outside the `oneof`.
- **Villain:** still overrides `send()`; "try `ciMode: false`" is still there; the sealed-sender
  risk row still says the server cannot see the sender.
- **Demo:** Beat 3 still cannot produce "withheld"; QR scanning is still assumed; "seen by" never
  fires in Beat 1; there is no stock client to show; the fork marker still has false positives.
- **The pitch** still overclaims. **Plaintext retention** is unchanged, and the rewrite makes it
  worse (§4.5).

## 4. New problems the rewrite introduces

### 4.1 `CheckedStore` conflicts with the approved Mathlib split

As written, `Rec := Record ChatPayload Digest Aci` (links are a Mathlib `Finset`), and `Built` is
stated through `abs`, `heads hashRecord (abs c)` and `AcceptBuilt`, which are all Mathlib
definitions (`PLAN.md:256-263`). So `Impl.lean` cannot be in the Mathlib-free library.

A `public meta import` of Mathlib would allow Prop fields without initialising Mathlib at
runtime. But Lake still compiles and links the meta-imported objects, `Crdt` would have to be
converted to `module` files, and the closure gate would report false positives. That route is
worse than the split.

**Recommended: keep the certificate with the code, stated without Mathlib.** This was verified
by building it (`/tmp/zrdt-diff-checkedstore/pkg`).

- **In `Zrdt`** (core and Std only):
  - a public `RawStore`. The plan's "private to the module" would block `Refine.lean`.
  - a Mathlib-free `structure Built`: keys are hashes, every record has the store's group, the
    head cache equals the keys nothing links, and an accept-order witness (newest first) whose
    members are exactly the map's values. Closure follows.
  - `CheckedStore := {raw; built}`, `empty`, and `accept` with `rawAccept_built`. The prototype
    proof is about 100 lines with core and Std only, axioms `[propext, Classical.choice,
    Quot.sound]`. The generated C passes the store straight through, because the proof is
    erased.
  - **One worklist** `acceptAll` that inserts **only through the checked `accept`**. Build
    `merge`, `open` and `salvage` from it, so `Built` holds by construction. A bug in the worklist
    can then only cause rejections or leftovers, never an unchecked store.
  - `zrdtd`'s table holds `CheckedStore` values. "Every handle is checked" is then enforced by the
    type in the shipped code, which the pasted type-level proposal wants.
- **In `Crdt`:** `toSpec`, a spec-side hash with `hashSpec (toSpec r) = hashRecord r`, `abs`, the
  bridge `Built → AcceptBuilt ∧ heads correct ∧ no collision`, and the refinement theorems.
- **Fallback, at no cost:** move the subtype into `Crdt` and have the daemon hold raw stores.
  Then "every handle is checked" holds only for the model and needs an extra theorem about the
  dispatcher.

Supporting changes:

- **Canonical links.** Without a canonical form, the same record with its links in another order
  is a different `Rec` with the same hash, so `accept` reports a false `COLLISION`. Use a strictly
  sorted, deduplicated array built by the single record constructor (strict decode rejects
  non-canonical blobs), or `Std.ExtTreeSet`.
- **Consider `Std.ExtTreeMap Digest Rec` for the store** (core Std, extensional `=`, sorted
  `toList`). It makes equality statements usable, fixes the order of `heads`/`missing`/blob
  output (§1.6 of the review), and keeps the same accept proof (verified). The cost is O(log n)
  lookups, which is fine for chats.
- **`Digest`.** Core 4.35 gives `Vector UInt8 32` a lawful order (`TransOrd`, `LawfulEqOrd`). For
  a ByteArray-backed digest, compare `bytes.data.toList`. `Crdt` lifts it to `LinearOrder` for
  `Finset.sort`.
- **Mistakes in the PLAN text.** `Built` uses `abs` before it is defined (`Refine.lean`, on
  `CheckedStore`). `c.heads.toFinset` does not exist for `Std.HashSet`.

### 4.2 Statements that are false as written

| Statement | Problem | Fix |
|---|---|---|
| `open_complete : AcceptBuilt (recordsOf b) → ∃ c, open b = .ok c` | Refutable. The model's `accept` (`Defs.lean:226-227`) inserts without checking collisions or the group. Counterexamples: two different records with one digest, a record from another group, and a malformed blob (if `recordsOf` is total, it gives `∅`). | `open b = .ok c ↔ ∃ g u, decodeBlob b = some (g,u) ∧ AcceptBuilt u ∧ ¬CollisionIn u ∧ ∀ r ∈ u, r.group = g` (with `abs c = u`, `c.group = g`) |
| `salvage_spec` | Same counterexamples. `salvage`'s type has no collision or wrong-chat outcome. | Same hypotheses; add those error cases |
| `encode_open` | False without a size bound: `accept` has no size check, so u32 frames wrap. `abs` forgets the group. | Add `card < 2^24` and a per-record size bound to `Built`, enforced in `accept` and `open` with an explicit status (or use varints). Pin the group in the statement. |
| `encode_injective` (§3.4 format) | Still false. A 2^32-byte body wraps its length field (concrete counterexample). | With the approved commitment payload the record is `group ‖ commit ‖ u32 nlinks ‖ links ‖ author`. Every field is fixed-size except one array of fixed-size elements, so **`Function.Injective encode` becomes true with no bound**. A size bound is then only needed for the blob framing. |
| `built_fetched … ∨ CollisionIn` | The disjunct can never hold. Map keys are unique and each key is its record's hash, so a `CheckedStore` has no collisions. | State it without the disjunct, and add `built_noCollision`. This gives a stronger headline. |
| Missing pieces | `zrdt_open_status` has no `WRONG_CHAT`. The open result lists unverifiable records but not the dangling link digests, which the "·9ac1 is missing" banner needs. | Add both. |

### 4.3 Overclaims about what `open` catches

`RESTORE_PLAN` §2 says `open` rules out "a record removed from the middle, any altered record".

`open` catches:
- removing or altering a record that something links;
- a link pointing to nothing;
- a changed group;
- malformed bytes.

`open` does **not** catch:
- removing the newest record (a head);
- editing a head's body, timestamp, author or attachments;
- appending a forged record.

The document contradicts itself here, because a head edit is a tail replacement of length 1. The
same overclaim appears in `PLAN.md:493-495` (Beat 4, "one byte changed"), `APP.md:339` (the doctor
must remove a *linked* record) and `PLAN_HUMANS.md:76-78`.

**Stale references to fix:**
- `zrdt_check`/`check` (`PLAN.md:69`; RESTORE §1 and §6.3);
- `zrdt_reaches` (`PLAN.md:336`, `APP.md:236`);
- the dropped theorem names `accept_rejects_names_missing` and `latest_reaches_all_own` (RESTORE
  §2);
- "`gap_indistinguishable` stated in RESTORE §2", which it is not.

**Also:** records kept by "keep what verifies" (salvage) should count as *imported*, not
confirmed. A middle record edited consistently can still verify.

### 4.4 "Confirmed" does not mean "written by its author"

Confirmation via `confirmed_exact` proves that the sender of a live message **holds** the record,
not that the record's claimed author wrote it. Verified attacks against the new text:

- **Relay forgery is unchanged, and the new design amplifies it.**
  1. Mallory links a fake "Alice" record F in her own live message.
  2. Every client asks Mallory for F, because requests now go 1:1 to the referencing sender. She
     serves F.
  3. Provenance has only two values (`'live' | 'imported'`, `APP.md:239`). RESTORE §3 calls a
     record live when it is "received through Signal from an authenticated sender", so F is
     **live**.
  4. F is therefore confirmed by construction and exempt from the foreign marker. It can also
     become "Alice's latest" (RESTORE §7), which hands Mallory the reference point used to judge
     Alice's other records.
  5. It also counts toward "seen by Alice" and can frame Alice with "sent as two versions".
- **Fields outside the hash can be injected into genuine records.** The hash covers group,
  timestamp, body, attachment digests, links and author. The responder supplies the rest of the
  DataMessage (quote, mentions, preview, sticker, `profileKey`), and APP processes it "through the
  normal path" as Alice. For group messages, `handleDataMessage.preload.ts:687-711` sets the
  received `profileKey` on the **sender's** contact. So a relay can overwrite Alice's profile key
  on other members' clients.
- **No rule on the receiving side can fix this.** "Alice wrote F and the server dropped it to
  Carol" and "Mallory forged F" give Carol identical views forever (`Forgery.lean`, `#guard`). Only
  something Alice's client *sends* can tell them apart.
- **The foreign marker gives false positives that the server controls.** "A's latest" is decided
  by receive order, and the server controls receive order. Example: delay Alice's genuine a4 until
  after Dave imports a dump containing her a5, which links a4. Then a4 becomes "latest", and the
  genuine a5 is marked "not confirmed by Alice".
- **A dump given by a member defeats stage 2.** The guarantee holds only against the server, or
  against a dump-giver who sends no live messages.

**Fix.** This keeps the teammate's "anyone can serve records" while restoring attribution.

1. **Provenance has three values:**
   - `live`: the Signal envelope sender (ACI‖device) equals the record's author;
   - `relayed(by X)`;
   - `imported`.

   Only `live` records count as an author's own.
2. **`authorConfirmed r`** ⇔ some `live` record from `r.author` reaches r, and no `live` record
   from `r.author` disowns r. Theorem: if an author's client disowns every accepted record in its
   own name that it did not create, then every author-confirmed record attributed to it was
   created by it (or two records collide). Add the W1/W2 indistinguishability `example` as the
   fourth limit.
3. **Never refuse a record in your own name.** M links F, so refusing F stalls everything after
   M. Instead accept F, alarm locally, and put F in a `disown` list in your next message:
   `ZrdtMeta { links, nonce, version, disown }`.
4. **With the commitment covering the full wire bytes,** content opened by any relayer is the
   author's content once the commitment is author-confirmed (by the binding property of the
   hash). So relaying stays allowed. Author-only resend through sendLog becomes a **fast path**
   for getting Alice's attribution immediately, not a requirement.
5. **Display:**
   - grey: nobody has confirmed holding it;
   - "held by X";
   - normal: confirmed by its author;
   - "not confirmed by A": decided by reachability, not receive order. Only flag records that
     are concurrent with one of A's live records.

   "Seen by" and the fork marker use only `live` records.
6. **Re-enter Desktop only at `handleDataMessage`,** with the scope predicate, and never through
   `onMessageReceived`'s delete, pin or poll branches. Do not apply `profileKey` (or other fields
   with side effects) from relayed messages.
7. **Fix the wording.** "Verified by hash, so it can come from anyone" (`PLAN_HUMANS.md:458-460`),
   "Signal's signatures check it" (`PLAN.md:26`, `PLAN_HUMANS.md:477`) and "confirmation by live
   links does the job without signatures" (RESTORE §7) all need rewording.

`ZrdtNotFound` is not "decisive", as PLAN_HUMANS claims.
- The server can drop the request or the reply.
- An honest member can say "not found" because another of their devices made the link, or
  because the store was salvaged, re-linked or erased.
- The message carries no request id and no heads.
- A not-found from a member for a digest that member linked is evidence of *inconsistency*, not
  of malice.

### 4.5 Restore is a privacy regression as written

Stock Desktop already has a plaintext "Export chat history". But that export:
- **omits disappearing messages** and erases content deleted for everyone;
- requires OS authentication;
- warns "do not share".

The zrdt dump keeps both kinds of messages, because the store only grows. It is designed to be
handed to others, including "a mirror, or the server", and it gives pre-join history to new
members. PLAN §1 and PLAN_HUMANS §9 still say zrdt data "rides inside Signal's encryption". Also,
**every group DataMessage's wire bytes contain the group master key** (`groupV2` = field 15,
`masterKey`), so raw bytes must never go into a dump.

**Fix:**
- **Commitment.** `commitment = SHA-256("zrdtP1" ‖ group ‖ author ‖ nonce ‖ DataMessage bytes
  without fields 15 and 200)`, computed in Lean, with the timestamp inside it.
- **Store the opening** (nonce plus bytes) as a new message attribute marked `erase` in
  `messageAttributesEraseBehavior`. That table is exhaustive, so TypeScript forces the
  classification, and Desktop's own delete and expiry paths remove it.
- **Dump = store blob + a content section keyed by digest.**
  - Leave out content for `expireTimer > 0`, deleted-for-everyone and view-once messages; the
    importer refuses such entries.
  - Give **structure-only** dumps to anyone who joined after a record was sent. That resolves
    their links without pre-join content, and also fixes the review's "newcomer pending forever"
    problem.
  - Require OS authentication and a "do not share" warning.
  - Drop "mirror or server" as transports unless the dump is encrypted.
- **Show unconfirmed imported records** in a collapsed section without avatars or live links,
  never inline under a member's name.
- **Say what is not covered:** link-and-sync and Signal backups carry no zrdt data, so a device
  restored the stock way has a full timeline and an empty store. Also say that the DAG metadata
  of expired messages persists.

### 4.6 Demo

- **Beat 5 needs a fourth desktop.** Make Dave a member from group creation (his mock phone
  receives beats 1–4) and link his desktop just before beat 5. Use four Bootstraps with
  `contactCount: 0`, and put the group in **every** phone's storage state. With the defaults,
  four Bootstraps create about 244 fake devices.
- **The time budget is already gone.** PLAN §8 allows 5 × 60 s = 300 s, which is the entire
  5-minute limit, with nothing left for the intro, the stock-client showing or the proof pitch.
  APP §9 says "target: 3 minutes" but its beats add up to 230 s.
  - Collapse beat 5 to the doctored variant only: import, then Alice writes, then Bob writes.
  - Have `doctor.ts` append the fakes **on top of** the genuine head, not replace the tail. Run
    it automatically on Bob's export, because digests depend on the live run and the file cannot
    be prepared in advance.
- **QR.** RESTORE §3 ("heads as a QR"), APP §7 and §9 and PLAN_HUMANS §6 still assume QR
  scanning. Desktop cannot decode QR, and on one Mac mini there is nothing to scan anyway. Use
  copy and paste.

## 5. The pasted proposal: state the theorems over `CheckedStore`

Agreed. The advertised statements should be about the type that runs, with the certificate
supplying the hypotheses. With §4.1's design, `Crdt/Merkle/Api.lean` states them over
`Zrdt.CheckedStore` using the bridge lemmas, and the gate and README pin those names.

Corrections to the proposed list:
- `CheckedStore.agree (h : c.heads = d.heads)`: with `Std.HashSet` heads, `=` compares bucket
  layout, so the hypothesis almost never holds between two phones. State it over contents, or use
  `ExtTreeSet` heads, where `=` is extensional.
- `open_complete` and `salvage_spec`: need the hypotheses from §4.2.
- `CheckedStore.confirmed`: says "held by the sender". Add `authorConfirmed` (§4.4) as the
  attribution result.
- Add `built_noCollision`, and state `built_fetched` without the collision disjunct.
- `heads_held` holds for honest senders at send time only (§4.4, `ZrdtNotFound`).

## 6. Net effect on the work

- **Phase A:** gains `authorConfirmed` and the W1/W2 limit example. `fetched_union` and
  `salvage_built` become internal obligations, as the proposal suggests.
- **Phase B:** becomes the `Zrdt`/`Crdt` split from §4.1:
  - a code `Rec` with canonical links and a commitment payload;
  - a Mathlib-free `Built`;
  - one checked worklist;
  - `ExtTreeMap` considered for the store;
  - the restated `open`, `salvage` and `encode` theorems;
  - `Api.lean` as the last deliverable.
- **Phase C:** becomes the `zrdtd` frame protocol, built on the Mac for darwin-arm64.
- **Phase D:** adds three-valued provenance, `disown`, erasable openings, a privacy-safe dump and
  the hook fixes from `REVIEW.md` §2.
- **Phase E/F:** four Bootstraps, the collapsed beat 5, and the time budget redone.

Evidence: verifier output in this session's workflow transcript `wf_a6b6ed1b-eee/journal.jsonl`.
Scratch builds are in `/tmp/zrdt-diff-checkedstore/pkg` (the Mathlib-free `Built` and
`AcceptProof.lean`) and `/tmp/zrdt-diff-*` (counterexamples, the commitment model, the forgery
model).
