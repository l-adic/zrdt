# JOIN_PLAN v2: adding members to a zrdt chat

Status: design, v2 of 2026-11-01. Not implemented. **Nothing here changes the demo build.** v1
(Martin's draft, commit `af76d2f`) is summarised in §11, with the reasons it changed.

## 0. For a reviewer starting cold

**What zrdt is.** A verified transcript-consistency layer for Signal group chats. Each message
carries hash links to the messages its sender had seen; a device's store is a set of such
records; merging is set union; the heads (records nothing links to) are the digest of a store.
The core is Lean 4, compiled and shipped as the daemon `zrdtd`; the theorems are about that
code. Threat model, fixed by the owner: the server and the network are the adversary; members are
honest or at least attributable; open groups with strangers are out of scope.

**What this document decides.** How a member added to a group with history gets a verified
store; what he may learn about the older history; and how every zrdt path that moves content
(resend, catch-up, restore) keeps Signal's own rule: **the content of a message goes only to the
accounts its author sent it to.**

**The design in five lines.**
1. The author writes its **audience** (the members it sends the message to, each with a hash of
   that member's identity key) into the message, as a new `DataMessage` field 201. `COMMIT`
   already covers every field except 15 and 200, so the record format does not change.
2. One Lean function, `SERVE`, decides every reply a member sends about its store. It releases
   content only if the content's **own committed audience** names the requester, with the
   identity key the requester uses now.
3. A newcomer gets the records sent to him, with content; the structure of records written after
   those; and bare digests for the older records they link to. His heads equal the responder's
   (proved), so compare codes still work.
4. zrdt reads no group revision and no join revision. A lying server cannot widen anyone's
   audience after the author froze it.
5. zrdt adds no signature and no MAC. Copies are authenticated by Signal's own deniable channels.

**Read, in this order:**
1. `PLAN_HUMANS.md` §2–§5: the model, the definitions, the theorems, how proofs reach the code.
2. `review-2026-11-01/AMENDMENTS.md`: A4 (record and commitment), A7 (scope, hooks; the demo
   group is static), A8 (provenance, disown, resend), A9 (restore), A12 (claims, trusted base).
3. This document. §11 says what changed from v1 and why.
4. Reference scratch Lean, not built, no `sorry`: `docs/join-v2/Serve.lean` and `ServeTest.lean`
   (the responder against the real `CheckedStore`, `openingMatches`, `walk`), `Rel.lean` (the
   newcomer's view, Mathlib-free), `Dvs.lean` (optional MAC tags, §10a).

**Verdicts on the three hypotheses the review tested.**
- **H1, designated-verifier tags as access control: refuted as stated.** A responder cannot
  check a tag made for someone else (only the author and that member hold the key), and a tag
  list in field 200 is not bound by the digest. What access control needs is an authenticated
  recipient list bound into the commitment: field 201.
- **H2, a blinded boundary keyed by revision: not needed.** Agreement relative to a boundary
  holds with no condition on the boundary (`agree_rel`, §7). Boundary entries are bare digests.
  A hash-checked boundary stays an option (§12.2).
- **H3, a server-supplied join revision makes an honest responder leak: confirmed.** v2 reads no
  revision anywhere.

**A leak in the build today.** The fork's `ts/zrdt/resend.preload.ts:334-336` (Mac mini,
`@762d31740`) passes `requesterWasMemberAtSend: () => conversation.hasMember(requesterAci)`, so any
member relays an opening to any current member, a newcomer included. It is latent because the
demo group is static (A7). `SERVE` replaces it (Phase 1, §10). **Do not allow membership changes
in zrdt groups before Phase 1 ships.**

## 1. Requirements and threat model

**Requirements** (the owner's words):
- **R1.** "If a member joins later, they should not get access to older data."
- **R2.** "If messages need to be signed to prove authenticity, they should be signed with a
  Designated Verifier Signature or something which has the same property Signal stresses: your
  signatures cannot be used against you."
- **R3** (design constraint). Reuse Signal's own mechanisms first. Add something only where Signal
  falls short, and say which gap it closes.

**What R1 means here.** The content of a message (its opening, or its plaintext) reaches an
account only if the message's author sent it to that account. A newcomer may learn:
- opaque digests of older messages that newer ones link to directly;
- the author and links (never the content) of a message he was not sent, if it was written after
  a message he was sent. This happens only in honest races (§6.4).

**What stays true from before:** same heads give the same history (`agree`); a store with a hole
is never accepted (`fetched`); provenance, disown and `CLASSIFY` work as in A8.

**Threat model.** The server and the network are the adversary. Members are honest or at least
attributable. **Non-goals:** denial of service (the server can always drop or delay); a member who
deliberately pastes, quotes or forwards old content; open groups with strangers.

## 2. What Signal already does, and where it stops

Checked against Signal-Desktop v8.33.0 and libsignal v0.105.4 (the version Desktop pins), with
scratch scripts against `@signalapp/libsignal-client` 0.105.4 on the Mac mini. Desktop paths are
relative to `ts/` (`protos/` sits at the top of the tree); libsignal paths say so.

| Signal fact | Status | Where |
|---|---|---|
| A newcomer cannot decrypt group messages sent before he joined: sender-key chains only ratchet forward, and his distribution message starts at the current iteration. | verified, tested | libsignal `group_cipher.rs:85-97, 228-287`; test: pre-join messages fail with "old counter" |
| A removed member loses the author's chain at the author's next send. | verified | `util/sendToGroup.preload.ts:440-452` |
| Signal's own retry re-sends only to accounts the author originally addressed, within 24 h. | verified | `util/handleRetry.preload.ts:196-202`; `sql/Server.node.ts:1688-1704` |
| New members get no history. History moves only between one account's devices (link & sync, backups). | verified | no history field in protos; `backups/index.preload.ts` |
| Live messages are authenticated deniably: sealed-sender MACs from identity-key agreement (v1 static keys, v2 per-recipient tags), and sender-key signatures under a fresh key bound to the author only by a pairwise message. | verified | libsignal `sealed_sender.rs:780-805, 1126-1156`; `protocol.rs:524-565` |
| A sealed-sender certificate is a server signature over identity only, not content. | verified | libsignal `sealed_sender.rs:197-340` |
| A sender addresses the members at compose time, intersected with the members at send time. Blocked and unregistered members are not addressed. | verified | `models/conversations.preload.ts:4450-4463`; `jobs/helpers/sendNormalMessage.preload.ts:526-596` |
| The revision on a message is read separately from its recipients (after an `await`), so it is only a proxy for "who was addressed". | verified | `conversations.preload.ts:4451` vs `4555` |
| "A receiver catches up to a higher revision before processing" is best effort. A failed or short fetch lets it process at an older revision. | partly true | `messages/handleDataMessage.preload.ts:264-295`; `groups.preload.ts:4278-4282` |
| A join revision (`joinedAtVersion`) is a plaintext value the server asserts. Log changes are not signature-checked; member ciphertexts are deterministic. A server can place a real add at an earlier revision for a client that was offline. | verified (H3) | `protos/Groups.proto:34`; `groups.preload.ts:4180-4330, 1064-1067, 6099-6236` |
| Invited and requesting members are never addressed; they become members at promotion. | verified | `util/getConversationMembers.dom.ts:21-29`; `groups.preload.ts:5608-5612` |
| Stock edits (of messages under 24 h old) go to the current members, so a newcomer receives the edited text. Quotes carry the quoted text. | verified | `util/sendEditedMessage.preload.ts:135-139`; `SignalService.proto` `Quote.text = 3` |

**Where Signal stops.**
1. **zrdt's own content paths have no rule.** Relay, catch-up and restore are zrdt's. The
   as-built responder leaks (§0).
2. **Two stock paths deliver older content to a newcomer:** edits and quotes.
3. **Every membership fact a client holds was asserted by the server.** Revisions and join
   revisions cannot decide access (H3).
4. **Signal gives a newcomer nothing to resolve links into older history with.** That is right
   for content, but zrdt needs it for links.

v2 reuses everything in the table and adds something only for these four gaps (§9).

## 3. The record and the audience

### 3.1 The record does not change

The record stays A4's `zrdt2`: `"zrdt2" ‖ group(32) ‖ commit(32) ‖ u32 nlinks ‖ sorted links ‖
author(16)`. The commitment stays `zrdtP1` over the `DataMessage` minus fields 15 and 200. There
is no revision field, no `zrdt3`, and no two-level hash. `encode_injective`, the vectors, `Built`
and the TypeScript stub are untouched.

### 3.2 The audience: `DataMessage` field 201

```
zrdtAudience (field 201, bytes) = n entries, 1 ≤ n ≤ 256, strictly increasing by aci
entry   = aci(16) ‖ keyTag(16)
keyTag  = first 16 bytes of SHA-256("zrdtK1" ‖ identity public key, 33 bytes serialized)
          or 16 zero bytes if the author had no key for that member
```

- **Who is in it.** The raw `conversation.membersV2[].aci` read at enqueue, in the same
  synchronous block that sets the recipients (`models/conversations.preload.ts:4450-4463`), intersected
  with `membersV2` at freeze (this drops members removed while the message was queued). Plus the
  author.
  - `getConversationMembers` is not used: it drops blocked and unregistered members, and then the
    audience would reveal the author's block list to the other addressees. Whether blocked members
    belong in the audience is a decision for kejace (§12.1).
  - Invited and requesting members are not in `membersV2`, so they are never in the audience.
- **The invariant the fork keeps:** the accounts a message is actually sent to are a subset of
  its audience. At every attempt, Desktop sends to the `sendStateByConversationId` keys
  intersected with the current members, and those keys are a subset of `membersV2` at enqueue.
- **The key tag.** The hash of the identity key the author holds for that member when it freezes
  the message. `SERVE` releases content only to a requester whose current identity key has the
  same tag. This stops a server that swaps a member's identity key from collecting that member's
  whole history through relays (§8.1). Stock Signal gives such a server only future messages and
  24 h of retries. The tag is a hash of a public key, so it is not a signature.
- **Why it is bound.** Field 201 is not 15 or 200, so it stays in the committed bytes. The opening
  contains it, `openingMatches` binds it to `record.commit`, and the commit binds it to the
  digest. Changing the audience of a real opening breaks the match (`audience_bound`, §7).
- **Who sees it.** Only holders of the opening, which are the addressees. It travels inside
  Signal's encryption. Stock clients ignore unknown field 201.
- **The cap.** A group with more than 256 members omits the field. Its messages then have no zrdt
  content path at all, only Signal's own. The value is a decision for kejace (§12.1).

### 3.3 Store blob, protocol version, migration

- **Store blob `zrdtS3`** = the `zrdtS2` layout plus two sections: the boundary digests (§6) and
  the audience table (digest → entries, filled only from openings `zrdtd` itself checked). Bounds
  as in A4. `zrdtS2` blobs still open, with an empty boundary and an empty audience table.
- **Protocol 3.** `ZrdtMeta.version = 3`. The frame protocol moves to 3 because `ACCEPT` gains an
  optional opening and new ops appear (§10).
- **Records without field 201** (written before the upgrade, by an older client, or in a group
  over the cap) have an **unknown audience**. No zrdt path sends their content to anyone; only
  Signal's own live delivery and 24 h retry do. Their structure is still served (§5).
- **Mixed versions.** An as-built responder still runs the leaky stub. Upgrade every member before
  allowing membership changes.

## 4. What each party sends, stores and checks

### 4.1 The author, sending

1. **At enqueue:** snapshot the raw `membersV2` ACIs into a new message attribute
   `zrdtAudience`. It survives retries and restarts.
2. **At freeze** (inside `conversation.queueJob` in `sendNormalMessage`, A7):
   - intersect the snapshot with `membersV2` now, and add the author;
   - load each member's identity key (`loadIdentityKey`); for any missing key, call
     `getKeysForServiceId` first (`textsecure/getKeysForServiceId.preload.ts:41`); if that fails,
     pass no key and the tag is zero;
   - call `AUDIENCE` with the (aci, key) pairs. `zrdtd` returns the field-201 bytes (the host never
     hashes, A4);
   - add field 201 to the `DataMessage`, then `COMMIT`, then `ACCEPT` with the opening, then
     persist `message.zrdt` as in A7.
3. **Every attempt** sends the frozen bytes. Recipients stay inside the audience.

The author stores its opening in `zrdtOpening` (A4), as today.

### 4.2 Every member, receiving live

- As A7, except that `ACCEPT` passes the opening. `zrdtd` checks it with `openingMatches` and, if
  it holds exactly one well-formed field 201, records the audience in its table. The audience is
  kept after the content is erased: it is membership metadata the holder already knew.
- A missing or malformed field 201 never rejects a record. It only means "audience unknown".
- Phase 3: keep the original sender-key message bytes (`zrdt_skm`, captured in
  `MessageReceiver.#decryptSealedSender`, `textsecure/MessageReceiver.preload.ts:1744-1773`). They are
  erased with the message (expiry, delete for everyone, view-once) and pruned after 14 days.

### 4.3 A responder (any member, the author included)

1. It receives a `ZrdtResendRequest{digests or catch-up, since}` (§10.1), 1:1 or through the group
   (A8 routing).
2. **Host check, defence in depth:** the requester is a current member in this client's view. If
   the server falsifies this, the worst result is content the requester was already sent.
3. The host calls `ADDRESSED` to learn which openings to load, then `SERVE` with the requester's
   ACI (the Signal-authenticated sender of the request), the identity key Desktop holds for the
   requester, the request's `since`, and the openings and sender-key messages it holds.
4. It sends `SERVE`'s bytes verbatim, 1:1, to that same ACI, as `ZrdtServed`.
   **Nothing else carries an opening.** The only constructor of a `ZrdtServed` with content takes a
   `SERVE` reply, and a lint rule forbids building one elsewhere.

### 4.4 The requester, receiving a reply

`ACCEPT_VIEW` takes the reply's entries:
- **Addressed record with opening:** `zrdtd` checks the digest and `openingMatches`, accepts the
  record and records its audience. Provenance is `live` if the reply came from the record's author,
  otherwise `relayed(by)` until the author confirms it (A8). In Phase 3, if a sender-key message is
  attached, the host first runs `groupDecrypt` on it under the author's address; on success the
  copy is `live`. Side-effect fields are never applied (A8).
- **After** (structure only): accepted as A8's structure-only relay. Shown as "a message from A
  that was not sent to you".
- **Boundary digest:** added to the boundary if not held.

A record is accepted when each link resolves to a held record or a boundary digest (§6.2).

### 4.5 Exports (A9, revised)

- **To your own account:** everything (records, boundary, audiences, openings). This is the
  analogue of Signal's link & sync.
- **To another account X:** exactly `SERVE`'s reply for X, using X's identity key, with an empty
  `since`. X imports it with `ACCEPT_VIEW`; records start `imported` (A9).
- Sender-key messages are never exported; they are bound to a device.

## 5. Serving: one rule, in Lean

`serve c q held` answers requester `q = (aci, identity key, since)` from store `c`.

- **`seats aud q`**: the audience `aud` has an entry with `q.aci` and the tag of `q`'s key, and
  that tag is not zero.
- **`entitled q r`**: the audience of `r` seats `q`. The audience comes from a matching opening if
  the host passed one, otherwise from `zrdtd`'s table.
- **`vis`**: the records `q` is entitled to that are not reachable from `q.since` (§6.5).
- **`up`**: every stored record that reaches a `vis` record. It is computed by walking links
  backwards from the `vis` records (the existing `walk` and `linkedBy`).

Each stored record `r` with digest `d` gives at most one entry:

| Entry | When | Carries |
|---|---|---|
| `addressed r o s` | `r` is in `vis` | the record; the opening `o` only if it matches `r.commit` **and its own committed audience seats `q`**; the sender-key message `s` only together with such an opening |
| `after r` | `r` is not in `vis` but is in `up` | the record (structure), never content |
| `boundary d known` | `r` is not in `up`, and `d` is linked by an `up` record or is a head | the digest only. `known` says whether the audience is known (it excludes `q`) or unknown |
| nothing | otherwise | |

- A **per-digest request** (gap repair, A8) uses the same classification, restricted to the
  digests asked for. A boundary entry carries no links, so a requester cannot crawl older history.
- **Channels for content, in order of preference.** Each one is Signal's or is gated by `SERVE`:
  1. Signal's live delivery.
  2. Signal's own retry: the author's sendLog re-send, within 24 h, to original addressees only.
  3. Phase 3: a forwarded original sender-key message, attached by `SERVE` next to an addressed
     opening. libsignal verifies the author's signature, and it decrypts only on a device that
     holds the chain and missed that message.
  4. The author's own `SERVE` reply. It arrives 1:1 from the author, so provenance is `live`. This
     extends Signal's 24 h rule using the audience in the author's own opening, with the key-tag
     check.
  5. Another member's `SERVE` reply. Provenance is `relayed(by)` until the author confirms (A8).
- **Strict mode** (optional, per group, off by default): a `SERVE` flag that releases content only
  from the author's own daemon. Non-authors then send structure only.

## 6. A newcomer's store

### 6.1 Starting

- Desktop starts when its own ACI appears in `membersV2`. A server lie here causes at most a
  useless request (denial of service).
- It sends `ZrdtResendRequest{catch-up, since}` 1:1 to the adder, who is the sender of the
  Signal-authenticated group-update message that added it (for an invite it accepted itself, any
  member). After a timeout it asks two more members.
- Live records that arrive meanwhile wait in `zrdt_pending` (A7).

### 6.2 The relative store

- `RawStore` gains a **boundary**: a set of digests, disjoint from the store's keys.
- **Accept, relative.** A record is accepted when each link is a held record or a boundary
  digest. Everything else about `accept` is unchanged.
- **Heads** are the held digests and boundary digests that no held record links to.
- **Promotion.** If a later reply delivers a full record for a boundary digest, and its links
  resolve, the record replaces the digest.
- **A boundary digest is member-vouched.** The newcomer cannot check it, because he has no
  preimage. A member who lies can hide a record from him (incompleteness, which is attributable to
  that member and never a leak). Boundary digests are accepted only from `SERVE` replies that came
  1:1 from a current member.

### 6.3 What he learns

- the records sent to him, with content;
- `after` structures (§6.4);
- opaque digests for the older records those link to directly, and for older heads.

The digests are pseudorandom, because the commitment is salted. No former member's ACI is shown.
The count of boundary digests is visible; Signal already reveals a similar count through the
iteration in a newcomer's sender-key distribution message.

### 6.4 Honest races: `after` entries

A member whose client had not yet applied the add can write a message that links a message sent
to the newcomer but is not itself sent to him. That message reaches him as an `after` entry:
author and links, no content. It is needed to keep the newcomer's heads equal to the responder's.
Nothing rejects the writer: there is no revision-order check.

### 6.5 Removal and re-add

- **Removal.** Signal resets the author's sender key at its next send. A removed member is not in
  later audiences, and responders answer current members only.
- **Re-add.** Desktop archives the old store (it stays readable in the UI), saves its heads as
  `since`, and opens a new relative store. Every request it sends carries `since`. `SERVE` leaves
  out records reachable from `since`, so the messages written while he was away come back as
  digests, not as `after` structures. Content stays per message: he gets content from both
  intervals that he was sent, and none from the gap.
- `since` rests on the requester's own client. A client that omits it learns the authors and
  links, never the content, of the messages written while it was out (§12.6).

### 6.6 Other devices of the same account

Entitlement is per account. The identity key is per account (a linked Desktop receives it at
provisioning), so a device linked later gets what its account was sent. This matches link & sync.
That device still cannot decrypt old sender-key messages.

### 6.7 Compare codes

By `served_heads` (§7), a newcomer who has caught up holds exactly the responder's heads. Compare
codes between old and new members match.

## 7. What gets proved

Two kinds of theorem. **Running-code theorems** are about the functions `zrdtd` runs; they are
the ones that stop a leak caused by a bug. **Spec theorems** are about the abstract model
(`Crdt/Merkle`) and say what a store means.

### 7.1 Running code: `core/Zrdt/Serve.lean` (Mathlib-free)

The scratch `docs/join-v2/Serve.lean` proves the first three for an audience of plain ACIs. v2
restates them with key tags.

- **`serve_content`** (proved in scratch). Every opening in a reply opens a stored record, and its
  own committed audience seats the requester. Every sender-key message travels with such an
  opening.
  ```lean
  theorem serve_content (h : Entry.addressed r o s ∈ serve c q held) :
      (∃ d, c.get d = some r) ∧ (s.isSome → o.isSome) ∧
      ∀ op, o = some op → openingMatches r.group r.author r.commit op = true ∧
        ∃ aud, audienceOf op = some aud ∧ seats aud q = true
  ```
  It does not mention `zrdtd`'s audience table, `since`, or any host flag, so no stale cache, host
  bug or server input can widen it.
- **`serve_content_exact`** (to prove). With an empty `since`, the content in a reply is exactly
  the reference set: the held openings that match their stored record and whose own audience
  seats the requester, each with its held sender-key message. With any `since`, it is a subset.
  This is the noninterference statement: content does not depend on the audience table, the
  structure entries, or anything the server can influence.
- **`serve_after`** (proved in scratch). An `after` entry is a stored record in the backward walk
  from the `vis` records. With `mem_reachersOf` (`ClassifyFast.lean`), it reaches a record sent
  to the requester.
- **`serve_boundary`** (proved in scratch). A `known` boundary digest is a stored record whose
  audience is known and does not seat the requester, and which is outside that walk, so it
  reaches nothing sent to him. This is the "no hidden hole" statement for known audiences.
- **`audience_bound`** (to prove). Two openings that both match one commit have the same
  audience, or SHA-256 has a collision. Proof: `openingMatches_spec`, `splitOpening_eq`, and
  injectivity of the fixed-size prefix.
- **`run_serve_content`** (to prove, like `acceptRecord_accepted`, `Proto.lean:752`). The same as
  `serve_content`, for the frame op `SERVE` that the daemon runs.
- **`acceptRel` and the relative store** (to prove). `rawAcceptRel_built`, `acceptView_built`,
  `acceptAll_sound` relative to the boundary, and `encode_reopens` for `zrdtS3`. With an empty
  boundary they are today's theorems.
- **Tests (`#guard`).** From `docs/join-v2/ServeTest.lean`: a pre-join record goes to Bob as a
  boundary digest only; Carol's stale-view record goes as `after`; its author gets the content; an
  opening whose audience was rewritten to add Bob fails `openingMatches` and is never served. New:
  a requester with a changed identity key gets no content; a re-added member with `since` gets the
  gap as digests; **H3 regression:** v1's rule (serve when `revision ≥ joinRev`) releases Carol's
  revision-8 opening when the server says Bob joined at 5, and `serve` does not.
- **Satisfiable and rejecting.** A named example instantiates each main theorem on that store,
  with every hypothesis discharged. A named example proves that a reply giving Bob the pre-join
  opening violates `serve_content`'s conclusion.

### 7.2 Spec: `Crdt/Merkle/Rel.lean`

`docs/join-v2/Rel.lean` proves these Mathlib-free over abstract records and digests. They are to
be ported onto the spec's `Record` and `Store`.

- **`agree_rel`.** If a view (full records `F`, boundary `B`) has the same heads as a closed
  store `S`, every full record reachable from the view's heads is in `S`, or two records collide.
  **It needs no condition on `B`.** This is why v1's revision check and H2's two-level hash are
  not needed.
- **`served_heads`.** The view a responder serves for any predicate `vis` (full records: those
  reaching a `vis` record; boundary: the other records linked by them, or heads) has exactly the
  responder's heads. No collision hypothesis.
- **`served_closed`**, **`served_tight`.** The served view is closed relative to its boundary,
  and tight when the store is.
- **`served_boundary`.** A boundary digest is the digest of a record that reaches no `vis`
  record.
- **`newcomer_agree`.** A tight view with the served heads holds only records of the responder's
  store, or two records collide.
- **Bridge `serve_abs`** (to prove, with `walk_spec`). When every stored record's audience is
  known, the records and boundary in `serve`'s reply are `ServedF` and `ServedB` for
  `vis r := entitled q r ∧ ¬ reachable from q.since`.

### 7.3 Advertised theorems

- New in `Crdt/Merkle/Api.lean`: `CheckedStore.agree_rel` and `Serve.serve_content`.
- The 11 existing advertised theorems are restated for a store with a boundary. With an empty
  boundary they say exactly what they say today. The Comparator challenge is updated to match,
  and Comparator is run only as the final step.

### 7.4 Deniability

No theorem is needed. `COMMIT`, `encode`, `AUDIENCE` and `SERVE` take no secret key: the key tag
hashes a public key. Anyone who holds the content, the nonce, the links and the public keys
computes the same bytes. Deniability of live messages, sender-key messages and pairwise messages
is libsignal's, in the trusted base. If the optional MAC tags of §10a are adopted, `tag_symmetric`
states that the designated reader computes the same tag.

## 8. Why no pre-join data reaches a newcomer

### 8.1 Against a lying server

| Attack | Why it fails |
|---|---|
| Replay old group envelopes to the newcomer. | Signal: his sender-key state starts at the current iteration; earlier messages fail with "old counter". |
| Send a retry request in his name for old timestamps. | Signal: the sendLog has no row for him (`handleRetry.preload.ts:196-202`). |
| H3: tell an offline responder that Bob joined at revision 5 when he joined at 9; Carol wrote at revision 8. | `SERVE` reads no revision. Carol's opening commits an audience without Bob, so he gets a boundary digest. |
| Forge a zrdt request in a member's name. | Requests are 1:1 Signal messages; the requester ACI is Signal-authenticated. |
| Swap a member's identity key and request his history. | The key tag in each audience is for the key the author held. Content goes only to a requester whose current key has that tag. |
| Show a responder that a removed member is still a member. | He gets only content he was already sent. Residual: `after` structures of later records that build on his (§12.5). |
| Show an author an early promotion of an invited or requesting account. | Signal itself then delivers that message live to him. zrdt never adds anyone to what Signal sent. Optional later fix: §10.3. |
| Drop or delay anything. | Denial of service, a non-goal. Gaps show (A12). |

### 8.2 Against a buggy responder

Whatever the host passes to `SERVE` (any opening, any cached audience, any `since`, any classification
it expected), `serve_content` holds: an opening leaves only if it opens a stored record and its own
committed audience seats the requester's ACI and key. A wrong opening fails `openingMatches`. A stale
cache affects structure entries only. What remains a host duty:
- pass the Signal-authenticated requester ACI and that requester's current identity key, and send
  the reply to that same ACI;
- send no opening outside a `SERVE` reply (one constructor, plus a lint rule);
- on the author's side, build the audience from the enqueue snapshot and the freeze-time members,
  never from the members at a later send. A TypeScript test pins "recipients ⊆ audience ⊆
  `membersV2` at enqueue ∪ {author}".

### 8.3 Signal paths the fork closes

- **Edits.** An edit of message `r` goes to `r`'s audience intersected with the current recipients,
  not to `conversation.getRecipients()` (`sendEditedMessage.preload.ts:135-139`). For a message with
  an unknown audience, the fork uses the original `sendStateByConversationId` keys, read before
  line 187 overwrites them.
- **Quotes.** If some current recipient is not in the quoted message's audience, or the audience is
  unknown, the quote is sent with its id and author only: no text, body ranges or attachments.
  Receivers who hold the original fill these in from their own copy
  (`messages/copyQuote.preload.ts:47-150`). A newcomer sees "original not found".
- **Not closed:** members on stock clients (Android, iOS, stock Desktop) in the same group still
  send edits and quotes the stock way. A member can paste old text on purpose.

### 8.4 Sharing older messages by choice (optional, later)

v1's §6 is kept as an optional extension. An author may send one of its own older messages to a
member who was not in its audience, by explicit action, 1:1. `SHARE` returns the opening only for
a record the requester's own daemon wrote (`share_scoped`). The receiver keeps it outside the store,
as "shared history". Signal's own Forward already covers most of this need.

## 9. What comes from Signal, what from zrdt, what stays trusted

| Property | From | Mechanism |
|---|---|---|
| A newcomer cannot read older group ciphertext | Signal | sender-key forward ratchet |
| Retries go only to original addressees | Signal | sendLog by recipient (24 h) |
| No history for new members | Signal | none exists |
| Live messages authenticated, deniably | Signal | sealed-sender MACs, sender-key signatures |
| History between one account's devices | Signal precedent | link & sync; zrdt own-account export |
| zrdt relays, catch-up and exports send content only to addressees | **zrdt** | field 201 + `SERVE` (closes gap 1) |
| A swapped identity key cannot collect relayed history | **zrdt** | key tag in field 201 (closes a gap zrdt itself would open) |
| Edits and quotes carry no older content to newcomers | **fork rule** | §8.3 (closes gap 2) |
| Access never depends on a server-asserted membership fact | **zrdt** | no revision read; the author's frozen audience (closes gap 3) |
| Older links resolve without content; heads still compare | **zrdt** | relative store, boundary digests, `served_heads` (closes gap 4) |
| A relayed copy authenticated as the author's | Signal, Phase 3 | forwarded sender-key message; otherwise A8 confirmation |

**Trusted** (beyond A12: the Lean compiler and runtime, the frame codec and protobuf scan, the
TypeScript client, SHA-256 collision resistance):
- **libsignal:** the forward ratchet; sender-key signatures and `groupDecrypt` checking them; the
  deniability of sealed-sender MACs and of the uncertified sender-key signing key.
- **Signal's server, for one thing:** the member list an author's client sees when it composes and
  freezes a message. Signal already trusts the server for exactly this. The server is not trusted
  for revisions, join revisions, the change log, or anyone's join point.
- **Identity keys:** Signal's trust-on-first-use and safety numbers. The key tag inherits them.
- **New small parsers:** reading field 201 (`audienceOf`, `parseAddressees`) joins the unproved
  protobuf scan.
- **Host duties:** §8.2; the audience snapshot; `since` on the requester side; passing only
  member `SERVE` replies to `ACCEPT_VIEW`; erasing sender-key messages with their message; not
  applying side-effect fields of late copies; the edit and quote rules.
- **Members:** honest or attributable. Boundary digests are member-vouched (§6.2).

## 10. Wire, frame ops, staging

### 10.1 Wire

```proto
message DataMessage { ...; optional bytes zrdtAudience = 201; }      // §3.2; inside the commitment
message ZrdtResendRequest { bytes groupId = 1; repeated bytes digests = 2;
                            repeated bytes since = 3; optional bool catchup = 4; }
message ZrdtServed { bytes groupId = 1; bytes entries = 2; }           // SERVE's reply, verbatim
message Content { oneof content { ...; ZrdtServed zrdtServed = 203; } }
```

`ZrdtResend` (Content 201) is no longer sent; it is still parsed. `ZrdtNotFound` (202) stays.

### 10.2 Frame ops (protocol 3)

| Op | Name | Request | Reply |
|---|---|---|---|
| `0x07` | `ACCEPT` (changed) | as before ‖ `u8` (1: an opening follows) | as before; records the audience of a matching opening |
| `0x11` | `AUDIENCE` | `u32` n ‖ n × (aci ‖ `u8` hasKey ‖ key(33)) | field-201 bytes; `TOO_LARGE` over 256 |
| `0x12` | `SERVE` | chat ‖ own aci ‖ requester aci ‖ key(33) ‖ since (`digests`) ‖ `u8` all ‖ wanted (`digests`) ‖ `u8` strict ‖ held items (digest, opening?, author device and sender-key message?) | entries |
| `0x13` | `ADDRESSED` | chat ‖ aci ‖ key(33) | digests whose stored audience seats them |
| `0x14` | `ACCEPT_VIEW` | chat ‖ entries | one result per entry |

`OPEN`, `MERGE`, `SALVAGE` and `ENCODE` read and write `zrdtS3`. `HEADS` covers held records and
boundary digests. Entry encoding: a kind byte, then the record bytes (addressed, after) or the
digest and a `known` byte (boundary); an addressed entry adds an optional opening and an optional
(author device, sender-key message).

### 10.3 Staging

- **Today (demo day):** nothing. The leak is latent in a static group.
- **Phase 1, the content gate.** Field 201, `AUDIENCE`, `ACCEPT` with opening, `SERVE`,
  `ADDRESSED`; `resend.preload.ts` calls `SERVE` and the stub is deleted; the edit and quote rules;
  exports through `SERVE`. Needs no store change. A Phase-1 requester ignores boundary entries, so
  a newcomer's pre-join links stay pending, as today. Membership changes no longer leak.
- **Phase 2, the newcomer.** The relative store, `zrdtS3`, `ACCEPT_VIEW`, catch-up on self-add,
  archive and `since` on re-add, the boundary row in the UI.
- **Phase 3, Signal-native relays.** Sender-key message capture and forwarding. Defence in depth:
  it covers only devices that hold the chain and missed the message, within libsignal's limits
  (2000 skipped keys, 5 chain states, a 25,000-iteration jump), and not pairwise-fallback sends.
- **Later, optional:** MAC tags (§10a); sharing by choice (§8.4); strict mode; an `ATTESTED`
  gate, where the adder writes the add into a zrdt record on Signal's own group-update message and
  authors address only members whose add they hold. That gate would close the early-promotion
  residual of §8.1 at a cost in liveness.

## 10a. Designated-verifier signatures: a signature that can't be used against you

**The principle.** Signal's authentication is deliberately deniable: a message convinces the person
who received it that you sent it, and nobody else. Anything zrdt adds must keep that. In one line:
if you need a signature from me, you can check it, and you can't use it against me.

**v2 adds no signature, no MAC and no new key.** Every authentication is Signal's:

| What is authenticated | How | Why it is deniable |
|---|---|---|
| A live message and its links | sealed-sender v1 static-key MAC, v2 per-recipient tag | both are MACs from identity-key agreement; the recipient could compute them |
| A forwarded original (Phase 3) | the sender-key signature, checked by `groupDecrypt` | the signing key is fresh and uncertified; it reaches members only in a pairwise message. Forwarding creates no new artifact |
| The author's own re-send | a 1:1 Signal message | pairwise, designated-verifier |
| A relayed copy | not authenticated by itself; `relayed(by)` until the author's own live messages confirm it (A8) | it proves nothing to anyone |

The record, the commit and the key tags are hashes that anyone holding the inputs recomputes. They
are no evidence of authorship. Two things would break deniability, and v2 does neither:
signatures under identity keys, and treating the server-signed sealed-sender certificate as bound
to content.

**If a gap ever needs tags: the MAC form (optional extension E1).** The gap is a copy that must be
shown as the author's when no forwarded sender-key message works and the author is not online:
pairwise-fallback sends, devices linked later, evicted keys, imports. The construction copies
sealed-sender v2's per-recipient tag, with zrdt's own label:

```
K_AX  = HKDF-SHA256(ikm = X25519(a, X_pub), salt = group, info = "zrdt-dv-v1" ‖ A_aci ‖ X_aci)
tag_X = HMAC-SHA256(K_AX, "zrdt-dv1" ‖ group ‖ A_aci ‖ X_aci ‖ digest)
```

- Desktop computes `X25519(a, X_pub)` with libsignal's `PrivateKey.agree` on its identity key pair
  (`signalProtocolStore.getIdentityKeyPair`) and passes only `K_AX` to `zrdtd`. The raw agreement
  never leaves one audited module, because sealed-sender v1 also uses it.
- The author computes one tag per audience member and carries the list in field 200, outside the
  digest (the tag is over the digest). Holders keep the list and attach `tag_X` when they relay to
  X. X checks it and stores the result with the record, so a later key change does not orphan it.
- **Deniable:** X derives the same `K_AX` from `(x, A_pub)`, so X could have made any tag that
  passes his check. `reader_can_forge` in `docs/join-v2/Dvs.lean` proves the witness form; HMAC and
  HKDF there match RFC 4231 and RFC 5869 vectors over the shipped SHA-256. Unforgeability by anyone
  else is the PRF and Diffie–Hellman assumption, in the trusted base beside SHA-256.
- **Never for access control.** A responder cannot check a tag made for someone else (H1).
- Cost: 48 bytes per member per message (ACI plus tag), in field 200.

**The OR-proof form (not adopted, kept for reference).** A Schnorr OR-proof ("Alice or Carol knows
the key") is publicly checkable, so anyone who sees it learns that Alice and Carol were talking:
less deniable than the MAC. libsignal exposes no scalar arithmetic, so it needs our own curve code.
Its completeness and deniability were proved in Lean over an abstract group (Lean v4.35.0, Mathlib
v4.35.0, axioms `[propext, Quot.sound]`; not in the build):

```lean
import Mathlib
variable {F G : Type*} [Field F] [AddCommGroup G] [Module F G] (g : G)

/-- What the verifier recomputes for one branch from response `s` and challenge `e`. -/
def recommit (pk : G) (e s : F) : G := s • g - e • pk
structure Sig (F : Type*) where (eA eC sA sC : F)
/-- The check: the two branch challenges must add up to the hash of the recomputed commitments. -/
def verifies (H : G → G → F) (A C : G) (σ : Sig F) : Prop :=
  σ.eA + σ.eC = H (recommit g A σ.eA σ.sA) (recommit g C σ.eC σ.sC)

/-- Alice signs for Carol: real Schnorr on her branch, simulated branch for Carol. -/
def signAlice (H : G → G → F) (a : F) (C : G) (rA eC sC : F) : Sig F :=
  let RA := rA • g; let RC := sC • g - eC • C; let eA := H RA RC - eC
  ⟨eA, eC, rA + eA * a, sC⟩
/-- Carol forges "Alice's" signature with the roles swapped, using her own key. -/
def forgeCarol (H : G → G → F) (c : F) (A : G) (rC eA sA : F) : Sig F :=
  let RA := sA • g - eA • A; let RC := rC • g; let eC := H RA RC - eA
  ⟨eA, eC, sA, rC + eC * c⟩

theorem alice_verifies (H : G → G → F) (a : F) (C : G) (rA eC sC : F) :
    verifies g H (a • g) C (signAlice g H a C rA eC sC) := by
  simp only [verifies, signAlice, recommit]
  have : (rA + (H (rA • g) (sC • g - eC • C) - eC) * a) • g
      - (H (rA • g) (sC • g - eC • C) - eC) • (a • g) = rA • g := by
    rw [add_smul, mul_smul]; abel
  rw [this]; ring

theorem carol_forges (H : G → G → F) (c : F) (A : G) (rC eA sA : F) :
    verifies g H A (c • g) (forgeCarol g H c A rC eA sA) := by
  simp only [verifies, forgeCarol, recommit]
  have : (rC + (H (sA • g - eA • A) (rC • g) - eA) * c) • g
      - (H (sA • g - eA • A) (rC • g) - eA) • (c • g) = rC • g := by
    rw [add_smul, mul_smul]; abel
  rw [this]; ring
```

## 11. Design history: what was tried and why it changed

- **v2 (this document, 2026-11-01): the author's audience, committed.** Chosen after a review that
  checked v1's Signal facts against source and compared four designs (below).
- **v1: the revision cut (Martin's draft, `af76d2f`).** Each record carried the sender's
  `groupV2.revision` (`zrdt3`); `joinRev(Bob)` came from the group's change log; a record was
  "post-join" if its revision was at least `joinRev`; `accept` checked that links never point to a
  higher revision; the boundary was a set of structures (author, revision, links) checked by hash
  and revision; catch-up filtered by revision; authors could share older messages; DV signatures
  were proposed (§10a). It changed because the facts it rested on did not hold:
  - catch-up before processing is best effort (§2), so the revision-order check would reject
    honest writers whose group fetch failed;
  - the revision on a message is read apart from its recipients, and blocked members are not
    addressed, so "revision ≥ joinRev" is not "sent to Bob";
  - `joinRev` is a plaintext value the server asserts, the change log is not signature-checked,
    and member ciphertexts are deterministic, so a lying server can make an honest responder leak
    (H3; the H3 regression test in §7.1 encodes it);
  - boundary structures named former members (v1 §12.3).

  **Kept from v1:** the boundary (now opaque digests), catch-up (now `SERVE`), "content only by
  the author's choice" (now the author's committed audience, plus optional sharing), the §10a
  principle and its proofs, and the review brief.
- **Alternatives weighed in the v2 review** (four designs; three judges scored them 8–8.5, 4.5–7,
  4–6 and 4–7):
  - **Addressed-only audience in field 201.** Chosen: no format change, no new cryptography,
    Signal's own retry rule made portable, the content theorem proved from the opening itself,
    compare codes kept for newcomers. Grafts from the others: the key tag (from the slot design's
    identity binding), the noninterference statement and H3 regression test (from the hardened
    design), the quote rule (from the attested design), mandatory `since` on re-add.
  - **v1 hardened:** `zrdt3` with a revision label and a two-level hash, so a newcomer can check
    each boundary entry; openings only from authors; non-author relays only as forwarded
    sender-key messages, made safe by a fork rule that resets the sender key whenever a send
    leaves out a chain holder. Not chosen: relays then fail for pairwise-fallback sends and devices
    linked later; cross-account restore was dropped; the reset rule changes Signal's sender-key
    policy; the author's "addressed" flag read `sendStateByConversationId`, which edits overwrite
    (`sendEditedMessage.preload.ts:187`); and a format change to carry a label the server controls.
  - **Addressee slots:** per-member designated-verifier MACs hashed into the record, so a
    requester proves he was addressed and a newcomer can prove he was not. Not chosen: new
    cryptography on every message, 16 bytes per member in every record, a store refactor to
    leaf-or-full nodes, and a newcomer who sees the whole older message graph. Its MAC
    construction is kept as E1 (§10a).
  - **Attested membership:** the adder writes the add into a zrdt record carried on Signal's
    group-update message, and a member is entitled to records that causally follow his add. Not
    chosen: a server that withholds a removal record, or fakes a promotion to one member, makes
    relays leak; it is coarser than addressing; it needs the adder to run the fork. Its quote rule
    is kept, and its `ATTESTED` gate is a later option (§10.3).
- **A member-authored join record with a Merkle root** (first draft, before v1). The adder wrote a
  hashed record naming the newcomer, with a Merkle root over every digest it reached; pre-join
  links were resolved by inclusion proofs. Dropped because Signal already announces joins, and it
  needed a Merkle tree, a new announcement and an extra sending rule. Its one advantage, a
  member-attested join point, no longer matters: v2 uses no join point.
- **Signatures inside records.** Rejected: a signature under a long-term key makes every message
  non-repudiable to anyone, which contradicts Signal's deniability (§10a).
- **A sending rule** ("don't send to a newly added member until you hold the join record").
  Unneeded: the author's frozen audience decides, whatever order things arrive in.
- **"Hide pre-join content in the UI."** Rejected as not a security boundary. Content must never
  reach the newcomer's device.
- **A lineage proof (SNARK) over the prefix.** Unneeded under this threat model: the members who
  would produce it already vouch for the history by building on it.

## 12. Review brief

The reviewer should try to break the design, then harden it. Known weak or unproven points:

1. **Decisions for kejace.**
   - Blocked members in the audience. Including them (the default) hides block lists from the
     other addressees, but lets a blocked member receive the author's messages through relays,
     which stock Signal would not send him. Excluding them reveals the block list. Padded
     designated-verifier slots (§11) would do both, at a high cost.
   - The cap of 256 members. Above it there is no zrdt content path.
   - Strict mode (author-only content) as the default, or off.
2. **Boundary digests are member-vouched.** A newcomer cannot check them (§6.2). A two-level
   record hash would let him, at the cost of a format change. Decide whether incompleteness
   attributable to a member is acceptable.
3. **Unknown audiences.** Records without field 201 have no zrdt content path. A newcomer gets
   them as `known = false` boundary digests. `serve_boundary`'s "no hidden hole" covers only
   known audiences.
4. **The key tag.** A member who reinstalls without restoring his identity key loses relayed
   history, as in Signal. A member the author had no key for gets a zero tag and only Signal's own
   paths. Check that Desktop's stored key for the requester is the key that authenticated the
   request.
5. **Removed member plus a lying server.** If a responder is made to believe a removed member is
   still a member, `SERVE` can give him `after` structures (authors and links, never content) of
   later records that build on records he was sent.
6. **`since` rests on the requester's client** (§6.5). Is metadata about the gap, never content,
   an acceptable cost of a dishonest re-added member?
7. **The author's member view is the server's.** An early promotion faked in one author's view
   makes Signal deliver live to that account, and zrdt follows. The `ATTESTED` gate (§10.3) is the
   fix; it costs liveness.
8. **The relative store re-proofs** (`BuiltRel`, relative accept order, `zrdtS3`, the 11
   advertised theorems) are the critical path and are not started. Phase 1 does not need them.
9. **Phase 3 is fragile.** Sender-key messages must be decrypted outside the envelope pipeline,
   in the right queue; a consumed key turns the late original into a silently dropped duplicate
   (`textsecure/MessageReceiver.preload.ts:2019-2023`). It must never be the only path.
10. **The theorems in §7.** Check each statement against the code it names; check that
    `serve_content_exact` really excludes every server-influenced input; check that the bridge
    covers `since`.

Deliverable: a written verdict with the facts that decide it, and the smallest set of edits to this
document that makes it sound.
