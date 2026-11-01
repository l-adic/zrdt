# JOIN_PLAN: adding members to a zrdt chat

Status: design for after the demo, not yet reviewed or implemented. Revised 2026-11-01.

## 0. For a reviewer starting cold

**What zrdt is.** A verified transcript-consistency layer for Signal group chats. Each message
carries hash links to the messages its sender had seen; a device's store is a set of such
records; merging is set union; the heads (records nothing links to) are the digest of a store.
The core is Lean 4, compiled and shipped as the daemon `zrdtd`; the theorems are about that
code. Threat model, fixed by the owner: members are honest or at least attributable; the server
and the network are the adversary; open groups with strangers are permanently out of scope.

**Read, in this order:**
1. `PLAN_HUMANS.md` §2–§5: the model, the definitions, the theorems, how proofs reach the code.
2. `review-2026-11-01/AMENDMENTS.md`: the approved decisions this document builds on. A4 (record
   format and the salted content commitment), A7 (scope; the demo group is static), A8
   (provenance `live | relayed | imported`, disown, resend routing), A9 (restore and privacy,
   structure-only dumps), A12 (claims and trusted base).
3. `review-2026-11-01/REVIEW.md` §2.9: the note that membership changes were undesigned.
4. `Crdt/Merkle/Defs.lean` and `Integrity.lean`: the spec as it exists (`Record`, `Store`,
   `Closed`, `heads`, `Reach`, `Complete`, `Tight`, `Fetched`, `accept`, `build`,
   `fetched_agree`, `fetched_build`). The revision field, the boundary and the theorems in §7
   below do not exist in the repository yet.

**What this document decides:** how a member added to a group with existing history gets a
verified store, what they may and may not learn about the earlier history, and how older
messages can be shared with them by choice. §11 records the alternatives that were tried and
why they were dropped; §12 is the brief for reviewing it.

**Signal facts this design relies on, and their status:**
- Verified by the team against Signal-Desktop v8.33.0 (`REVIEW.md`): group messages are
  GroupV2 `DataMessage`s whose `groupV2` context holds the master key and a `revision`; the
  commitment in A4 omits that field because of the master key; stock clients ignore unknown
  proto fields; sender-key chains move only forward, so a newcomer cannot decrypt earlier
  iterations.
- Stated from memory, **to be verified by the reviewer** (§2 and §8): that a receiver which sees
  a higher revision fetches the group changes before processing the message, and what it does if
  that fetch fails; that a sender addresses only its own revision's member list; that the
  revision of the change that added a member is readable by every client, including one that
  joined later; how pending, invited and requesting members are numbered.
 The demo group is static
(`review-2026-11-01/AMENDMENTS.md` A7), and `REVIEW.md` §2.9 left membership changes as future
work. Names follow `AMENDMENTS.md`: a record is `(group, commit, links, author)` plus, from this
plan, `revision`; its content is the `opening` (nonce ‖ DataMessage bytes); provenance is
`live | relayed(by) | imported`; the library is reached through `zrdtd` frame ops.

## 1. What a newcomer needs

Bob is added to a group that already has history.

1. **A verified history that starts at his join.** Everything written after he joined is in his
   store and checked like anyone else's. Links into the older history resolve without his holding
   its content.
2. **One answer to "is this before or after Bob joined?"**, the same on every device.
3. **No old content by accident.** Content from before the join reaches Bob only when its author
   chooses to share it. Catch-up and resend never send it.
4. **Shared content is authenticated to Bob, and only to Bob.**
5. **Fast start.** Bob catches up in one round trip.

## 2. What Signal already does

Signal announces joins, and this plan builds on that rather than adding a second announcement.

- **A join is a group change.** The group state lives on Signal's server as a numbered sequence
  of revisions. Adding Bob moves the group from revision `N` to `N+1`.
- **Everyone is told.** The adder sends a group-update message to the new member list, Bob
  included. A client that missed it fetches the change log from the server.
- **Every group message carries its sender's revision.** `DataMessage.groupV2.revision`. A
  receiver that sees a higher revision than its own fetches the missing changes before it
  processes the message.
- **Delivery follows the sender's view.** A client addresses each message to the member list at
  its own current revision. A sender still at `N` does not address Bob.

## 3. The cut is the revision

**Record change.** Each record carries the sender's group revision, inside the hash:

```
"zrdt3" ‖ group(32) ‖ revision(u32) ‖ commit(32) ‖ u32 nlinks ‖ links ‖ author(16)
```

The commitment (A4) deliberately leaves out Signal's `groupV2` field, because it holds the group
master key. The revision sits inside that field, so it is copied into the record explicitly. All
fields keep a fixed size apart from the links array, so `encode_injective` still holds with no
size bound. On a live message, the receiver checks that `record.revision` equals the envelope's
`groupV2.revision`.

**The rule.** Let `joinRev(Bob)` be the revision of the change that last added Bob, read from the
group's change log. A record `r` is **post-join for Bob** when `r.revision ≥ joinRev(Bob)`, and
**pre-join** otherwise.

- The rule is a field of the record, so every device gets the same answer.
- It matches Signal's delivery exactly: a message was addressed to Bob if and only if its sender
  was at a revision that includes him.
- If Bob was removed and added again, the most recent add counts.

**Revision order.** `accept` checks one new thing: every linked record has a revision no higher
than the record's own. Honest clients satisfy this automatically, because a client processes a
message only after catching up to its sender's revision, and from then on writes at that revision
or later. The consequence: from a pre-join record you can only reach pre-join records, so older
history never leads to newer content.

## 4. Bob's store and the boundary

Bob's first post-join messages link to older messages he will never read. To accept them, he
needs to know those links are real and are pre-join.

**The boundary is a set of structures.** A structure is a record without its content:
`(group, revision, commit, links, author)`. Because the commitment is salted (A4), a structure
reveals nothing of what was said. When a member answers Bob's request for an older message, it
sends the structure only. Bob checks two things himself:

- the structure hashes to the digest that was linked, so it is the real record;
- its revision is below `joinRev(Bob)`, so it really is pre-join.

Nothing here rests on the member's word. A pre-join structure is a leaf for Bob: he does not
fetch what it links to.

**Accept, relative to the boundary.** A record is accepted when each of its links resolves to a
held record or to a boundary structure. Everything else about the store is as before:
`CheckedStore`, the certificate, `open`, `salvage`, compare codes, confirmation.

**What Bob learns about the past:** the authors, revisions and links of the older messages that
newer ones point at directly, and nothing else. That is the review's accepted metadata cost (A9),
limited here to the frontier.

## 5. Fast catch-up

Bob sends any member `CATCHUP{group, heads}`. His heads start empty. The responder reads
`joinRev(Bob)` from its own group state and returns, in one reply:

- every record reachable from its heads, not reachable from Bob's heads, with
  `revision ≥ joinRev(Bob)`, together with its opening;
- the structure of each pre-join record those records link to, with no opening.

Bob accepts the batch in any order and ends with his verified post-join history.

## 6. Sharing older messages, by choice

Bob already holds the structure of the older messages that matter to him, so he can ask about a
specific one. He asks its **author**. The author decides, with "never" as the default and a
setting such as "share my history with new members" as the opt-in.

If the author agrees, their client sends Bob a 1:1 Signal message `ZrdtResend{record, opening}`.
The envelope's sender is the record's author, so provenance is `live`. Bob checks
`COMMIT(opening) = record.commit` against the structure he already holds.

**This is already a designated-verifier signature.** Signal's pairwise channel is authenticated
with keys only the author and Bob share, so it convinces Bob and is deniable to everyone else. No
new cryptography is needed. A copy from anyone other than the author is shown as `relayed(by)`.

Shared older messages are kept outside Bob's verified store, as annotations on their boundary
structure, and shown in a separate "shared history" section. The store stays exactly the
post-join history.

## 7. What gets proved

- **`revision_le_of_reach`.** In a store where links respect revision order, everything reachable
  from a record has a revision no higher than that record's. This is the claimed-timestamp
  theorem from the earlier timestamping discussion (`time_le_of_reach`, proved in scratch), with
  the revision as the clock. Consequence: from a pre-join record you only reach pre-join records.
- **`boundary_sound`.** A boundary structure that hashes to a linked digest and has revision below
  `joinRev` is that pre-join record, or there is a collision.
- **`catchup_scoped`.** Every opening in a catch-up or resend reply to Bob belongs to a record
  with `revision ≥ joinRev(Bob)`; pre-join links come back as structures. This theorem is about
  the responder function that runs, and it is the one that stops a leak caused by a bug.
- **`newcomer_agree`.** If Bob's heads match a member's, Bob's store is exactly that member's
  post-join records, and his boundary is exactly the pre-join records they link to, or there is a
  collision. This is `fetched_agree` relative to a boundary, with the same proof.
- **`share_scoped`.** An honest client sends a pre-join opening only for a record it authored,
  only 1:1, and only to the member who asked.

Later, with the symbolic adversary model: under any interleaving the server can produce,
pre-join content enters a newcomer's knowledge only through an author's share.

## 8. What this relies on

- **Signal's server, for membership.** Revisions are numbered by Signal's server, which is the
  only authority on group state. A malicious server could show different members different member
  lists. That is Signal's existing trust model for membership, and this plan inherits it rather
  than fixing it. Fixing it would mean putting membership changes into the hashed history.
- **Signal's delivery rule.** Clients address messages by their current revision and process a
  message only after catching up to its sender's revision. This is what makes "addressed to Bob"
  and "post-join" coincide. It is a property of Signal's clients, stated here, not proved.
- **Honest members.** A member can still paste old content into a new message. No protocol can
  prevent that.

## 9. Implementation outline

- **Spec (`Crdt/Merkle/`).** `revision` in the record; `RevisionOrdered`; `PostJoin` as a
  comparison of revisions; `ClosedRel` and `FetchedRel` relative to a boundary of structures; the
  theorems of §7.
- **Code (`core/Zrdt/`).** Record format `zrdt3`; the revision-order check in `accept`; a boundary
  of structures in `RawStore` and in `Built`; `acceptRel`; `catchupResponse`.
- **Frame ops.** `CATCHUP{chat, joinRev, heads}`; `ACCEPT_BOUNDARY{chat, structure, joinRev}`;
  `OPEN` keeps the boundary.
- **Desktop.** Copy `groupV2.revision` into the record on send. Check it on receive. Read
  `joinRev` from the group's change history (path to confirm on checkout). Add a
  `zrdt_boundary(conversationId, digest, structure)` table, the "shared history" section, and
  the share setting.

## 10. Open questions

- **Removals.** Signal already keeps removed members out going forward, through sender-key
  rotation and the member list. Nothing in this plan needs removal records.
- **Disappearing messages.** A shared older message with `expireTimer > 0` follows A9's rule and
  is not shared.
- **Default policy.** "Never share" matches Signal today. Opt-in per author is the natural
  extension, and it is a product decision.

## 10a. Designated-verifier signatures: a signature that can't be used against you

This is a highlight of the design and belongs in the pitch. It is proposed, not yet adopted.

**The principle.** Signal's authentication is deliberately deniable: a message convinces the
person who received it that you sent it, and nobody else. Any signature zrdt adds must keep that.
An ordinary signature under a long-term key breaks it. A **designated-verifier signature**
convinces exactly one chosen reader: Alice makes it for Carol; Carol checks it and knows Alice
made it, because she knows she didn't; everyone else sees something Carol could have made herself.
In one line: if you need a signature from me, you can check it, and you can't use it against me.

**Where it is needed.** Live messages are authenticated by Signal already. Copies are not:
- relayed records (A8): Carol receives Alice's message from Bob and today must trust Bob or wait
  for Alice's chain; with a tag Alice made for Carol in every copy, Carol verifies Alice directly;
- imported dumps (`RESTORE_PLAN.md`): author-verified on import for messages sent while the
  importer was a member;
- shared older messages (§6): the 1:1 Signal channel already is designated-verifier; a tag keeps
  the property if the copy is forwarded again.

**Construction, and whether Signal's keys allow it.** Checked on 2026-11-01 against the libsignal
node bindings (`node/ts/EcKeys.ts`) and Signal-Desktop v8.33.0
(`ts/SignalProtocolStore.preload.ts`):
- Every account has a long-term X25519 identity key. Desktop can read its own pair
  (`getIdentityKeyPair`) and every contact's public key (`loadIdentityKey`); group members' keys
  are present once pairwise sessions exist, which sender-key distribution requires. libsignal
  exposes `PrivateKey.agree(PublicKey)` (X25519 agreement), `PrivateKey.sign` /
  `PublicKey.verify` (XEdDSA) and `serialize`.
- **Shared-key MAC: implementable today, no new keys.** `k = agree(a, C) = agree(c, A)` is
  computable only by Alice and Carol. Alice attaches `tag_Carol = HMAC(KDF(k), digest)` for each
  member. Carol recomputes it; Bob can't; Carol could, so it is deniable. 32 bytes per member.
  This is the same shape as Signal's own 1:1 authentication, precomputed per reader so that
  copies carry it. Everything it needs is in the existing API.
- **Schnorr OR-proof ("Alice or Carol knows the key").** Publicly checkable form, about 128
  bytes per member. libsignal does not expose scalar arithmetic on identity keys, so this needs
  our own curve code over the exported key bytes and the Montgomery-to-Edwards conversion that
  XEdDSA uses. Possible, but custom cryptography; the MAC is the practical choice.
- Keys that do **not** work: the group master key and profile keys are shared with every member,
  so a MAC under them is forgeable by any member and attributes nothing; sender-key signing keys
  are per epoch and held inside libsignal records.

So the question "can Signal's keys do this" is settled: the MAC form needs nothing a Signal
client doesn't already hold. No special keys, no key exchange.

**What Lean proves.** For the OR-proof form, completeness (Alice's signature passes the check)
and deniability (Carol's forgery passes the same check) are proved as identities in an abstract
commutative group with field scalars, which is what an elliptic-curve group is; the whole proof
is `(r + e·a)·G − e·(a·G) = r·G`, twice. The code is below; it was checked on Lean v4.35.0 /
Mathlib v4.35.0 and depends only on `[propext, Quot.sound]`. It is not in the build. For the MAC
form there is nothing algebraic to prove; the formal content is the protocol statement in the
witness form used everywhere in zrdt: a tag that verifies was made by Alice, or by the verifier
itself, or here is a forgery. Unforgeability by anyone else is the discrete-log / PRF assumption
and stays in the trusted base, beside SHA-256.

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

**Cost and limits.** One tag per member per message, so a group of 20 adds under 1 KB; this is
the one per-member cost in the design. A tag exists only for members at send time, so a later
joiner or a fresh device verifies from its join forward, which matches §3. `accept` would gain one
check (`badTag` rejects a forged copy at the door, replacing A8's after-the-fact disown for
copies), and the certificate one conjunct.

## 11. Design history: what was tried and why it changed

- **A member-authored join record with a Merkle root** (first draft). The adder wrote a hashed
  record naming the newcomer and carrying a Merkle root over every digest reachable from its
  links; that record's digest was the newcomer's root; pre-join links were resolved by inclusion
  proofs. Dropped because Signal already announces joins: it had an edge case (a member who had
  not yet received the join record could send to the newcomer, and the message would count as
  pre-join), which needed an extra client rule; and it needed a Merkle tree and a new announcement
  message. Its one advantage, which the current design gives up and §12 asks the reviewer to
  weigh: `joinRev` was attested by a member in the hashed history, not read from the server.
- **Signatures inside records** (considered for authorship of copies). Rejected: a signature under
  a long-term key makes every message non-repudiable to anyone, which contradicts Signal's
  deniability. Per-recipient designated-verifier signatures were considered next (an OR-proof
  "Alice or Carol signed", about 100 bytes per member per message, or a shared-key MAC, 32 bytes);
  the OR-proof's completeness and simulatability were proved in Lean over an abstract group
  (§10a). Not yet adopted: §6 observes that a 1:1 Signal message from the author already is a designated-verifier
  channel, so sharing needs no new cryptography. Authorship of relayed copies otherwise follows A8
  (`relayed(by)` until the author's own chain confirms, plus disown).
- **A sending rule** ("don't send to a newly added member until you hold the join record").
  Made unnecessary by using the revision: Signal's own catch-up before processing gives it.
- **"Hide pre-join content in the UI."** Rejected as not a security boundary. Content must never
  reach the newcomer's device except by an author's share.
- **A lineage proof (SNARK) over the prefix.** Judged unnecessary under this threat model: the
  members who would produce it are the members already vouching by building on the history. It
  would matter only for outsiders or untrusted members, both out of scope.

## 12. Review brief

The reviewer should try to break the design, then harden it. Points known to be weak or unproven:

1. **Where `joinRev` comes from.** §3 reads it from the group's change log, which the server
   serves. If a responder trusts the server for `joinRev`, a malicious server can make an honest
   responder leak pre-join content by claiming the newcomer joined earlier. Decide: use the
   revision the responder itself observed when it applied the add; refuse to serve if it never
   observed it; or reinstate a member-authored attestation of `joinRev` (hybrid with §11's first
   draft). State what the design trusts the server for, and check it against A12.
2. **Membership intervals.** §3 uses "the revision of the change that last added Bob". A member
   added, removed and re-added legitimately received messages in the earlier interval; the rule
   calls them pre-join and `newcomer_agree` fails for them. The rule also has no upper bound: a
   removed member asking for catch-up. Define entitlement per interval and add the responder's
   membership check.
3. **Metadata in boundary structures.** A structure reveals the author ACI, revision and link
   shape of a pre-join message. That can name former members Signal would never show a newcomer.
   Decide whether that is acceptable, and whether responders must limit structures to digests
   directly linked by post-join records (so the newcomer cannot crawl the prefix).
4. **The revision-order check in `accept`.** An honest client whose group-state fetch failed can
   write at an old revision while linking newer records; every member then rejects its messages
   until it catches up. Assess the liveness cost and whether rejection is the right response.
5. **Consistency with the amendments.** The record format moves from `zrdt2` (A4) to `zrdt3`;
   `Built`, the store blob, vectors and the TypeScript stub all change. A9's structure-only dumps
   give a late joiner the whole pre-join structure; §4 gives only the frontier. Reconcile.
6. **The theorems in §7.** Check each statement is true as written, name the hypotheses the
   certificate must carry (`RevisionOrdered`, boundary soundness), and say which are about the
   spec filter (trivial) and which about the running responder (meaningful).
7. **The Signal facts marked "to be verified" in §0.** Check them against the pinned source
   (`ts/groups.ts`, `ts/textsecure/MessageReceiver.preload.ts`, `protos/Groups.proto`).

Deliverable: a written verdict (keep, hybrid, or revert to §11's first draft) with the facts that
decide it, and the smallest set of edits to this document that makes it sound.
