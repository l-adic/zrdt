# JOIN_PLAN v2: adding members to a zrdt chat

Status: **built**, v2 of 2026-11-01, after review round 1 (§12.1), the user decisions (§12.2)
and review round 2 (§12.3, a leak hunt on the built code). The code is on zrdt branch `join`
(draft PR l-adic/zrdt#3) and on the fork's branch `join` (draft PR
l-adic/signal-desktop-zrdt#7). `zrdtd` speaks frame protocol 4. Neither is merged to `main`.
**Nothing here changes the demo build.** v1 (Martin's draft, commit `af76d2f`) is summarised in
§11, with the reasons it changed. Where this document and a code header disagree on a byte
layout, the code header is right: `core/Zrdt/Proto.lean` (frame ops), `core/Zrdt/ChatStore.lean`
(`zrdtS3`).

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
accounts its author's client addressed when it froze the message, and only to the holder of the
identity key it addressed them under.** The addressed accounts are a subset of the accounts
Signal sends the message to at enqueue.

**The design in six lines.**
1. The author writes its **audience** into the message, as a new `DataMessage` field 201: each
   member with a hash (tag) of the identity key the author holds for it. Members Signal does not
   send to (blocked, seen as unregistered, no key) get the zero tag. `COMMIT` already covers every
   field except 15 and 200, so the record format does not change. Every record message carries
   field 201; an opening without a valid one is rejected.
2. One Lean function, `SERVE`, decides every reply a member sends about its store. It releases
   content only if the content's **own committed audience** seats the requester: his ACI with a
   non-zero tag of the identity key the responder holds for him.
3. The host **seals** each reply to exactly that key, the way sealed sender v1 seals its sender
   layer to the recipient's identity key (libsignal's own `agree`, HKDF and AES-GCM-SIV). If Signal
   later re-targets the session to a swapped key, the new key cannot read the content.
4. A newcomer gets the records sent to him, with content; the structure of records written after
   those; and bare digests for the older records they link to. Any responder, including a former
   newcomer, serves a view with exactly its own heads (proved), so compare codes still work.
5. zrdt reads no group revision and no join revision. Access follows the author's own membership
   view at enqueue and freeze, as Signal's live delivery does, and nothing else the server says.
6. zrdt adds no signature and no MAC. The seal authenticates nothing. Copies are authenticated by
   Signal's own deniable channels. Two Signal-flavoured additions were dropped in round 1 because
   they would leave evidence: keeping sender-key messages (the former Phase 3) and broadcast tags
   (E1).

**Read, in this order:**
1. `PLAN_HUMANS.md` §2–§5: the model, the definitions, the theorems, how proofs reach the code.
2. `review-2026-11-01/AMENDMENTS.md`: A4 (record and commitment), A7 (scope, hooks; the demo
   group is static), A8 (provenance, disown, resend), A9 (restore), A12 (claims, trusted base).
3. This document. §11 says what changed from v1 and in round 1, and why; §12.3 what round 2
   found in the built code.
4. The code. In `core/` (Mathlib-free, shipped as `zrdtd`): `Zrdt/Serve.lean` (the rule),
   `Zrdt/RelStore.lean` (the relative store), `Zrdt/ChatStore.lean` (closed or relative, and the
   blob `zrdtS3`), `Zrdt/Proto.lean` (the frame ops; its header fixes every byte). In `Crdt/Merkle/`
   (the spec, with Mathlib): `Rel.lean`, `RelSpec.lean`, `RelRefine.lean`, `ClassifyRel.lean`,
   `ServeAbs.lean`, `ServeAbsRel.lean`, `ServeExamples.lean`, and `Api.lean` (the advertised
   statements). `vectors/vectors.json` pins the bytes for the fork. §7 lists every theorem.
5. The scratch Lean in `docs/join-v2/` is kept for reference only: `Serve.lean` and
   `ServeTest.lean` were ported to `core/Zrdt/Serve.lean`, and `Rel.lean` to
   `Crdt/Merkle/Rel.lean` (the port drops the scratch's sent-to path, greenfield). `Dvs.lean` is
   kept only as HMAC/HKDF over the shipped SHA-256; its tag scheme is not adopted (§10a).

**Verdicts on the three hypotheses the review tested.**
- **H1, designated-verifier tags as access control: refuted.** A responder cannot check a tag made
  for someone else (only the author and that member hold the key). A tag list in field 200 is not
  bound by the digest. And (round 1) a tag list broadcast to the group is not deniable: every
  holder keeps `tag_X`, which only the author or X can compute, so a judge with one holder's device
  and X's key has a two-witness proof (§10a). Access control needs an authenticated recipient list
  bound into the commitment (field 201) and delivery bound to the checked key (the seal).
- **H2, a blinded boundary keyed by revision: not needed, and no help.** Agreement relative to a
  boundary holds with no condition on the boundary (`agree_rel`, §7). A hash check on
  `(revision, inner)` proves nothing exists: anyone can hash a made-up `inner`. Boundary digests are
  vouched by the member that served them, and contained (§6.2).
- **H3, a server-supplied join revision makes an honest responder leak: confirmed.** v2 reads no
  revision anywhere. All three round-1 breakers re-tested it against v2; it fails.

**A leak in the demo build.** The demo build's `ts/zrdt/resend.preload.ts:334-336` (fork branch
`zrdt`, `@762d31740`) passes `requesterWasMemberAtSend: () => conversation.hasMember(requesterAci)`,
so any member relays an opening to any current member, a newcomer included. It is latent because
the demo group is static (A7). On `join`, `SERVE` replaces it. **Do not change membership in a
group that runs the demo build.** JOIN is greenfield (§3.3): it replaces that build, and no group
mixes the two.

## 1. Requirements and threat model

**Requirements** (the owner's words):
- **R1.** "If a member joins later, they should not get access to older data."
- **R2.** "If messages need to be signed to prove authenticity, they should be signed with a
  Designated Verifier Signature or something which has the same property Signal stresses: your
  signatures cannot be used against you."
- **R3** (design constraint). Reuse Signal's own mechanisms first. Add something only where Signal
  falls short, and say which gap it closes.

**What R1 means here.** The content of a message (its opening, or its plaintext) reaches an
account only if the author's client seated that account (non-zero tag) when it froze the message,
and only the holder of the identity key it seated. A newcomer may learn:
- opaque digests of older messages that newer ones link to directly;
- the author and links (never the content) of a message he was not sent, if it was written after
  a message he was sent. This happens whenever an author's view of the membership lags the add:
  honest races cause it, and the server can prolong it (§6.4). Metadata only.

**What stays true from before:** same heads give the same history (`agree`); a closed store never
has a hole, and a relative store's only holes are its boundary digests, each vouched by a named
member (`fetched`, §6.2); provenance, disown and `CLASSIFY` work as in A8.

**Threat model.** The server and the network are the adversary. Members are honest or at least
attributable. Identity keys are trust-on-first-use: a server that substitutes a key on first
contact impersonates that member in Signal itself. zrdt inherits that and must not amplify it.
**Non-goals:** denial of service (the server can always drop or delay); a member who
deliberately pastes, quotes or forwards old content; open groups with strangers.

## 2. What Signal already does, and where it stops

Checked against Signal-Desktop v8.33.0 and libsignal v0.105.4 (the version Desktop pins), with
scratch scripts against `@signalapp/libsignal-client` 0.105.4 on the Mac mini; round-1 rows were
checked against the same Desktop tree. Desktop paths are relative to `ts/` (`protos/` sits at the
top of the tree); libsignal paths say so.

| Signal fact | Status | Where |
|---|---|---|
| A newcomer cannot decrypt group messages sent before he joined. The primary barrier is sealed sender v2's per-recipient key encapsulation and the pairwise sessions that carry sender keys: he has no slice of an earlier message. Second layer: sender-key chains only ratchet forward, and his distribution message starts at the current iteration. | verified, tested | libsignal `sealed_sender.rs` (SSv2), `group_cipher.rs:85-97, 228-287`; test: pre-join messages fail with "old counter" |
| A removed member loses the author's chain at the author's next normal group send, in the author's (server-supplied) view of the members. Partial sends skip this; only calling messages use them. | verified | `util/sendToGroup.preload.ts:430-452`; `jobs/helpers/sendCallingMessage.preload.ts:65,108` |
| Signal's own retry re-sends only to accounts the author originally addressed, within 24 h, to whatever identity key is current then. | verified | `util/handleRetry.preload.ts:196-202`; `sql/Server.node.ts:1688-1704` |
| New members get no history. History moves only between one account's devices (link & sync, backups). | verified | no history field in protos; `backups/index.preload.ts` |
| Live messages are authenticated deniably to outsiders: sealed-sender MACs from identity-key agreement (v1 static keys, v2 per-recipient tags), and sender-key signatures under a fresh key bound to the author only by a pairwise message. Inside the group, any holder of the author's chain can verify a sender-key signature; Desktop keeps the message only in flight. | verified | libsignal `sealed_sender.rs:780-805, 1126-1156`; `protocol.rs:524-565`; `textsecure/MessageReceiver.preload.ts:1744-1773` |
| A sealed-sender certificate is a server signature over identity only, not content. | verified | libsignal `sealed_sender.rs:197-340` |
| Identity keys are trust-on-first-use. Desktop accepts a changed key on receive at once, and trusts it for sending 5 s later. On 409/410 a send re-fetches bundles and re-encrypts the same plaintext to the key now current. | verified | `SignalProtocolStore.preload.ts:82, 1960-1967, 2208-2214`; `textsecure/OutgoingMessage.preload.ts:680-706` |
| A sender addresses the members at compose time, intersected with the members at send time. Blocked and unregistered members are not addressed, at every attempt. A server marks a member unregistered for 6 h by listing it in `uuids404`. | verified | `models/conversations.preload.ts:4450-4463`; `jobs/helpers/sendNormalMessage.preload.ts:526-596`; `util/getConversationMembers.dom.ts:34-40`; `util/sendToGroup.preload.ts:570-575`; `util/isConversationUnregistered.dom.ts:9,32` |
| The revision on a message is read separately from its recipients (after an `await`), so it is only a proxy for "who was addressed". | verified | `conversations.preload.ts:4451` vs `4555` |
| "A receiver catches up to a higher revision before processing" is best effort. A failed or short fetch lets it process at an older revision. | partly true | `messages/handleDataMessage.preload.ts:264-295`; `groups.preload.ts:4278-4282` |
| A join revision (`joinedAtVersion`) is a plaintext value the server asserts. Log changes are not signature-checked; member ciphertexts are deterministic. A server can place a real add at an earlier revision for a client that was offline, or hide a removal and re-add. | verified (H3) | `protos/Groups.proto:34`; `groups.preload.ts:4180-4330, 1064-1067, 3738-3778, 6099-6236` |
| Invited and requesting members are never addressed; they become members at promotion. | verified | `util/getConversationMembers.dom.ts:21-29`; `groups.preload.ts:5608-5612` |
| Stock edits (of messages under 24 h old) go to the current members, so a newcomer receives the edited text. Quotes carry the quoted text, body ranges and thumbnails. The wire quote is rebuilt from the message's `quote` attribute on every attempt, for sends and edits alike; `makeQuote` runs earlier, when Reply is clicked. | verified | `util/sendEditedMessage.preload.ts:109-139`; `jobs/helpers/sendNormalMessage.preload.ts:151, 700, 844-990`; `state/ducks/composer.preload.ts:949`; `SignalService.proto` `Quote.text = 3` |

**Where Signal stops.**
1. **zrdt's own content paths have no rule.** Relay, catch-up and restore are zrdt's. The
   demo build's responder leaks (§0).
2. **Two stock paths deliver older content to a newcomer:** edits and quotes.
3. **Every membership fact a client holds was asserted by the server.** Revisions and join
   revisions cannot decide access (H3).
4. **Signal gives a newcomer nothing to resolve links into older history with.** That is right
   for content, but zrdt needs it for links.
5. **Signal binds no reply to the identity key that was checked.** A send goes to whatever key is
   current when it is encrypted, re-fetched on 409/410. A rule that checks a key must also bind its
   content to that key.

v2 reuses everything in the table and adds something only for these five gaps (§9).

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
          or 16 zero bytes: a member Signal does not send this message to (blocked, seen as
          unregistered), or one the author has no key for
```

- **Who is in it.** The raw `conversation.membersV2[].aci` read at enqueue, in the same
  synchronous block that sets the recipients (`models/conversations.preload.ts:4450-4463`),
  intersected with `membersV2` at freeze (this drops members removed while the message was
  queued). Plus the author, with the tag of its own identity key.
  - Invited and requesting members are not in `membersV2`, so they are never in the audience.
- **Who is seated (non-zero tag).** Exactly the members in Desktop's own recipient set at enqueue
  (`getRecipients`: not blocked, not unregistered) for which the author holds a key, plus the
  author. Blocked and seen-as-unregistered members stay in the list with the zero tag: Signal
  sends them nothing, so zrdt gives them nothing, and since a zero tag also means "no key" the list
  does not reveal the author's block list. (This settles a question v2 left to kejace.)
- **The invariants the fork keeps,** pinned by a TypeScript test: seats ⊆ recipients at enqueue ∪
  {author}; the accounts a message is actually sent to, at every attempt, ⊆ audience.
- **The key tag.** The hash of the identity key the author holds for that member when it freezes
  the message. `SERVE` releases content only to a requester whose current identity key, in the
  responder's view, has the same tag, and the host seals the reply to that key (§4.3). Together
  they give content only to the holder of the key the author addressed: a server that swaps a
  member's key after the author froze cannot collect relayed history, not even by re-targeting a
  reply in flight. The tag is a hash of a public key, so it is not a signature.
- **Why it is bound.** Field 201 is not 15 or 200, so it stays in the committed bytes. The opening
  contains it, `openingMatches` binds it to `record.commit`, and the commit binds it to the
  digest. Changing the audience of a real opening breaks the match (`audience_bound`, §7).
- **Who sees it.** Only holders of the opening, which are the addressees. It travels inside
  Signal's encryption. Stock clients ignore unknown field 201. The tags show addressees which
  members got the zero tag, and that a member's key changed: public-key hashes, metadata only.
- **Required.** Every record message carries exactly one well-formed field 201. `zrdtd` refuses
  an opening without one (`NO_AUDIENCE`, §4.2), so every opening it accepts has an audience. And
  `ACCEPT` requires the opening, so every live record has its audience recorded.
- **The cap: 256 members** (user decision, §12.2). Over the cap `AUDIENCE` returns `TOO_LARGE`,
  and the client sends the message without zrdt fields: a stock Signal message, with no record
  and no zrdt content path.

### 3.3 Greenfield, store blob, protocol version

- **Greenfield** (user decision, §12.2). There are no zrdt messages from before JOIN and no older
  zrdt clients: every fork client runs the same protocol, and every record message carries field
  201. Nothing reads the demo build's `ZrdtResend` messages (Content 200, 201) or a top-level
  `zrdtS2` blob, and there is no migration, backfill or version gate. Stock Signal clients
  (members' phones, other platforms) still take part in the group, without zrdt fields (§8.3).
- **Store blob `zrdtS3`** (`core/Zrdt/ChatStore.lean`; `OPEN`, `SALVAGE`, `MERGE`, `ENCODE`).
  Numbers are big-endian:
  ```
  "zrdtS3" ‖ mode u8 (0 closed, 1 relative)
    ‖ n u32 ‖ n × (digest(32) ‖ voucher aci(16))           the boundary, sorted by digest
    ‖ m u32 ‖ m × (digest(32) ‖ len u32 ‖ field-201 value)  the audience table, sorted by digest
    ‖ the records, as a zrdtS2 blob, to the end
  ```
  A closed blob has `n = 0`. The boundary lists every digest the store took as a boundary digest,
  including those later promoted to a stored record (§6.2). The audience table holds only
  audiences `zrdtd` recorded from openings it checked, only for stored records, and only
  well-formed ones (every audience `zrdtd` records is). A blob reopens as exactly its store and
  audiences (`ChatStore.encode_reopens`, §7.1). Bounds as in A4.
- **Versions.** `ZrdtMeta.version = 3` on the wire. The `zrdtd` frame protocol is 4 (`VERSION`):
  3 added the join ops (§10.2), and 4 made `ACCEPT` always take the opening and gave
  `ACCEPT_VIEW` a mode and a pending list (round 2, §12.3). Host and `zrdtd` must match; the host
  checks at start.

## 4. What each party sends, stores and checks

### 4.1 The author, sending

1. **At enqueue:** snapshot the raw `membersV2` ACIs and the `getRecipients` set into a new message
   attribute `zrdtAudience`. It survives retries and restarts.
2. **At freeze** (inside `conversation.queueJob` in `sendNormalMessage`, A7):
   - intersect the snapshot with `membersV2` now, and add the author;
   - for each member in the enqueue recipient set, load its identity key (`loadIdentityKey`); for a
     missing key, call `getKeysForServiceId` first (`textsecure/getKeysForServiceId.preload.ts:41`).
     On a transient failure, do not freeze: the job fails and retries, as Signal's own send to that
     member would. Only a 404 (unregistered) gives the zero tag;
   - call `AUDIENCE` with (aci, key or none) pairs, none for members outside the enqueue recipient
     set. `zrdtd` returns the field-201 bytes (the host never hashes, A4), or `TOO_LARGE` over the
     cap, and then the message goes without zrdt fields (§3.2);
   - add field 201 to the `DataMessage`, then `COMMIT`, then `ACCEPT` with the opening, then
     persist `message.zrdt` as in A7.
3. **Every attempt** sends the frozen bytes. Recipients stay inside the audience.

The author stores its opening in `zrdtOpening` (A4), as today. A member whose key legitimately
changes between freeze and delivery forfeits zrdt relays of that message (Signal's own retry
still reaches the new key).

### 4.2 Every member, receiving live

- As A7, except that **`ACCEPT` always takes the opening** (lead decision, round 2): its request
  is `chat ‖ parts ‖ opening`, with no flag. `zrdtd` checks, in order: `NO_CHAT`; the opening
  matches the record (`openingMatches`, else `BAD_OPENING`); it holds exactly one well-formed field
  201 (else `NO_AUDIENCE`); then `accept`'s own checks. On a refusal nothing changes
  (`accept_refused`) and the host does not store the record; records that link it wait in
  `zrdt_pending` and show a gap, as for a link to a made-up digest (A12). On `OK` the audience is
  recorded under the record's digest (`accept_accepted`), so every record `ACCEPT` stores has its
  audience. The audience is kept after the content is erased: it is membership metadata the holder
  already knew.
- A record that arrives **without content** (a relayed structure, an `after` entry, the doctor's
  fakes in the demo) goes in with `ACCEPT_RECORD` (opening flag 0: stored as structure, no
  audience recorded) or `ACCEPT_VIEW` (§4.4). An opening passed to either is checked as
  `ACCEPT`'s. A structure-only record cannot be checked for field 201; that is harmless, because
  `SERVE` releases an opening only under its own audience (§5).
- A live record that waited in `zrdt_pending` is accepted later with its opening, so its audience
  is recorded too.
- No sender-key message is kept (the former Phase 3, dropped in round 1, §11).

### 4.3 A responder (any member, the author included)

1. It receives a `ZrdtServeRequest{requestId, digests or catch-up, since}` (§10.1), 1:1 or
   through the group (A8 routing).
2. **Host check, defence in depth:** the requester is a current member in this client's view. If
   the server falsifies this, the worst result is content the requester was already sent.
3. The host calls `ADDRESSED` to learn which openings to load, then `SERVE` with: the requester's
   ACI (the Signal-authenticated sender of the request); the identity key Desktop holds for the
   requester now; `since` = the request's `since` joined with this responder's own `since` for that
   account (§6.5); the wanted digests or catch-up; the export flag (§4.5); the group's strict
   setting (§5); this device's own ACI, its `live` digests and its disown set (A8 host state); and
   the openings it holds.
4. **Seal and send.** `SERVE`'s reply starts with a header: the requester's ACI, the tag of the key
   `SERVE` checked, and the request id. The only send path for it, `sendZrdtServed(reply, key)`,
   checks that the key's tag equals the header's, takes the destination ACI from the header, seals
   the entries to the key, and sends them 1:1:
   ```
   e      ← PrivateKey.generate()                       (fresh per reply)
   k      = HKDF-SHA256(ikm = e.agree(K), salt = e_pub ‖ K,
                        info = "zrdt-seal-v1" ‖ group ‖ requester aci ‖ request id)
   sealed = AES-256-GCM-SIV(k, nonce, entries, aad = header ‖ e_pub)
   ```
   This is the construction sealed sender v1 uses for its sender layer (ephemeral key agreement
   with the recipient's identity key), with libsignal's own primitives (`PrivateKey.agree`, HKDF,
   `Aes256GcmSiv`). The requester opens it with `agree(his identity private key, e_pub)`, on any
   device of his account. It gives confidentiality only: there is no authenticator and nothing
   anyone can show later, so R2 is untouched. If Signal re-targets the session to another key (a
   key accepted on receive, trusted for sending 5 s later, a 409/410 re-fetch), that key's holder
   gets bytes it cannot open. A host bug that sends to the wrong account does the same.
   Forward secrecy of a reply redirected that way rests on the requester's identity key, as for
   sealed sender v1; against the passive server, the Signal session's ratchet still applies.
5. **Nothing else carries an opening.** The only constructor of a `ZrdtServed` takes a `SERVE`
   reply, and a lint rule forbids building one elsewhere. **A zrdt request never triggers the
   sendLog re-send** (it encrypts to whatever key is current). Signal's own
   `DecryptionErrorMessage` retry stays as stock, with its own 24 h exposure.

### 4.4 The requester, receiving a reply

`ACCEPT_VIEW` takes a reply only if all of these hold, and the host drops it otherwise:
- it opens under this account's identity key, and its header names this account's ACI;
- its request id is one this device sent and has not completed (other devices of the account
  receive the reply too, and drop it);
- the responder's identity key has not changed since the request was sent (Desktop's identity
  record and `keychange` events).

The host then calls `ACCEPT_VIEW` with: the responder as voucher; the import flag (§4.5); the
**mode of the request it sent** (0 catch-up, 1 per-digest); the reply's entries, unchanged; and
**`pending`**: the records it holds pending whose missing links it asked for, a live one as an
addressed entry with its opening, a relayed one as `after`. `zrdtd` gives one result per entry,
reply entries first, then pending.

Per entry:
- **Addressed record with opening:** `zrdtd` checks the record bytes (`MALFORMED`) and the
  opening (`BAD_OPENING`, `NO_AUDIENCE`; in import mode also `EPHEMERAL`), accepts the record and
  records its audience. Provenance is host state: `live` if the entry is marked **author copy**
  and the reply came from the record's author; otherwise `relayed(by responder)` until the author
  confirms it (A8), even when the responder is the author. Side-effect fields are never applied
  (A8).
- **After** (structure only): accepted as A8's structure-only relay. Shown as "content not
  available from <responder>", never as "not sent to you": a responder that lacks the audience
  cannot tell.
- **Boundary digest:** taken only by a relative store, with the responder as voucher (the first
  voucher of a digest stays). A closed store takes none (result `IGNORED`). In per-digest mode the
  digest is kept only if it is stored or a stored record links it, counting records accepted in
  the same request; otherwise it is dropped again (`IGNORED`). The rule and its reason are in
  §6.2.

Records are accepted as one batch, in whatever order lets their links resolve to a held record or
a boundary digest (§6.2). A refused entry changes nothing. A record whose result is `MISSING`
stays pending, and the host asks for the digests listed. The gap marker for a wanted digest stays
open until content arrives or the author itself has been asked.

### 4.5 Exports (A9, revised)

An export file is outside Signal's encryption, so its content is always sealed to the one account
that may read it, exactly as a `SERVE` reply (§4.3). Both kinds are built in
`ts/state/ducks/zrdt.preload.ts` (Settings → Internal).

- **A9's exclusions hold for every export.** `SERVE`'s export flag refuses an opening whose
  committed `DataMessage` has field 5 (`expireTimer`) non-zero or field 14 (`isViewOnce`) set
  (`serve_export`, §7); deleted-for-everyone openings are already erased. `ACCEPT_VIEW` in import
  mode refuses them too (`EPHEMERAL`).
- **To your own account** (the analogue of Signal's link & sync): `{zrdtDump: 1, account, blob,
  content}`. `blob` is the store's `zrdtS3` (records, boundary, audiences). `content` is the
  openings `SERVE` gives the exporter's own account with the export flag, **sealed to the
  exporter's own identity key** (header: own ACI, own key tag, a random id). Import: the file
  must name this account, its header this account's ACI and key tag, and it must open under this
  account's key. Then `MERGE` of the blob, then each opening is checked. Another account's own
  export is refused, also with its `account` field rewritten (its content does not open). So
  **`MERGE` only ever takes the account's own export: no foreign store is merged into any store,
  relative or closed.** The blob's structure (digests, authors, links) stays readable, because
  the demo's beat-4 doctor edits it (§12.4).
- **To another account X:** `SERVE` for X, the same call a catch-up from X would make (own ACI =
  the giver's, requester = X's ACI, key = the identity key the giver holds for X, catch-up, empty
  `since` joined with the giver's own `since` for X, the export flag, the group's strict setting),
  **sealed to that key**: `{zrdtExport: 2, from, to, group, key, sections}`. It holds only what
  `SERVE` gives X: content X was sent, `after` structures, boundary digests. No new op was needed.
  X imports it like a catch-up reply: each section must name X's ACI and key tag and open under
  X's key; if X has no store, the export opens one as a first catch-up reply would (§6.1); then
  `ACCEPT_VIEW` with the giver as voucher, import flag 1, mode 0 (catch-up). Records start
  `imported` (A9); boundary digests are vouched by the giver and contained like any other (§6.2).
- **The importer keeps an opening only if it seats him**, under his own ACI and key tag, whoever
  made the file. This is a host check on the opening's own committed audience (the leak fix of
  round 2, §12.3). For a record whose opening came in an `ACCEPT_VIEW`, `ADDRESSED` gives the
  same answer (`acceptView_audiences`: the recorded audience is that opening's own;
  `run_addressed`). `zrdtd` has no import mode that checks the seat itself (§7.5).
- **Relays of disappearing messages** keep the message's timer, which starts when the receiver
  reads it, as for a late live delivery. Optional: refuse relays of a disappearing message older
  than its timer, measured from `sent_at`.

## 5. Serving: one rule, in Lean

`serve c me held q` answers requester `q = (aci, identity key, since, wanted, export, strict)`
from a responder with store `c`, own state `me` (its ACI, `live` digests, disown set, and its own
boundary, empty for a closed store) and the openings `held`.

- **`seats aud q`**: the audience `aud` has an entry with `q.aci` and the tag of `q`'s key, and
  that tag is not zero. **There is no author shortcut:** the author is seated by its own entry,
  under its own key.
- **`entitled q r`**: the audience of `r` seats `q`. The audience comes from a matching opening if
  the host passed one, otherwise from `zrdtd`'s table. A record whose audience the responder does
  not hold (it got the record without content) entitles no one.
- **`since`**: the requester's `since` joined with the responder's own `since` for that account
  (§6.5). Joining only shrinks what is shown.
- **`vis`**: the records `q` is entitled to that are not reachable from `since`.
- **`up`**: every stored record that reaches a `vis` record. It is computed by walking links
  backwards from the `vis` records (the existing `walk` and `linkedBy`).

Each stored record `r` with digest `d`, and each digest `d` of the responder's own boundary, gives
at most one entry:

| Entry | When | Carries |
|---|---|---|
| `addressed r o ac` | catch-up: `r` is in `vis`. Per-digest: `r` is wanted and `q` is entitled to it, whatever `since` says (`since` shapes structure, never content) | the record; the opening `o` only if it matches `r.commit`, **its own committed audience seats `q`**, for an export it neither disappears nor is view-once, and in strict mode the entry is an author copy; `ac` (author copy) only if the responder wrote `r`, holds it `live`, and has not disowned it |
| `after r` | `r` is not addressed but is in `up` | the record (structure), never content |
| `boundary d` | `d` is a stored record that is neither, or a digest of the responder's own boundary; and `d` is linked by an `up` record or is a head (per-digest: any wanted digest) | the digest only. No `known` bit on the wire: it would tell the requester whether the responder itself was addressed |
| nothing | otherwise | |

- A **per-digest request** (gap repair, A8) gives an entry for each wanted digest only. A boundary
  entry carries no links, so a requester cannot crawl older history.
- **Channels for content, in order of preference.** Each one is Signal's or is gated by `SERVE`
  and sealed:
  1. Signal's live delivery.
  2. Signal's own retry: `DecryptionErrorMessage` → sendLog re-send, within 24 h, to original
     addressees only, under the key current then. Stock; zrdt never triggers it.
  3. The author's own `SERVE` reply. Entries marked author copy arrive `live`. This extends
     Signal's 24 h rule using the audience in the author's own opening, with the key check and the
     seal.
  4. Another member's `SERVE` reply. Provenance is `relayed(by)` until the author confirms (A8).
- **Strict mode** (user decision: built, off by default, opt-in per group): a `SERVE` flag that
  releases content only in author-copy entries. A strict responder sends content as channel 3,
  never as channel 4. It is a setting each member's client keeps per group (Settings → Internal)
  and applies when it responds; nothing on the wire carries it (§12.2).

## 6. A newcomer's store

### 6.1 Starting

- Desktop starts catch-up whenever this device has no zrdt store for a group whose `membersV2`
  includes its own ACI (at startup, after a group update, or when a live record links history),
  not only on the transition into `membersV2`. It reads no join revision (`joinedAtVersion`):
  the trigger is "no store" (`needsCatchUp`, `ts/zrdt/catchUp.std.ts`). A server lie here causes
  at most a useless request (denial of service).
- It sends `ZrdtServeRequest{requestId, catch-up, since}` 1:1 to the adder, who is the sender of the
  Signal-authenticated group-update message that added it (for an invite it accepted itself, any
  member). After a timeout it asks two more members.
- The first catch-up reply decides the store: `NEW_RELATIVE` if it carries a boundary digest,
  `NEW` (closed) if not (a member from the start: every record it holds was sent to him). A re-add
  opens a relative store at once (§6.5). An imported export for this account (§4.5) opens a store
  the same way.
- Live records that arrive meanwhile wait in `zrdt_pending` (A7).

### 6.2 The relative store

- **Two kinds of store** (`ChatStore`, `core/Zrdt/ChatStore.lean`). A **closed** store is the
  `CheckedStore` of before, running the same code, so every closed theorem still covers it. A
  **relative** store (`RelStore`, `core/Zrdt/RelStore.lean`) is a raw store plus a **boundary**:
  digest → the ACI that vouched for it. A store stays the kind it was opened as.
- **Accept, relative.** A record is accepted when each link is a held record or a boundary
  digest (`rawAcceptRel`). Everything else about `accept` is unchanged; with an empty boundary it
  is `rawAccept` (`rawAcceptRel_empty`).
- **Heads** are the held digests and boundary digests that no held record links to.
- **Promotion.** If a later reply delivers a full record for a boundary digest, and its links
  resolve, it is accepted like any other. The digest stays in the boundary (a boundary only
  grows, so every record accepted over it keeps a valid accept order and the blob reopens);
  `boundaryDigests` are the boundary digests with no stored record, and those are what `HEADS`,
  `SERVE` and the UI mean by "the boundary".
- **Only a store opened by a catch-up reply, a re-add or an export for this account can be
  relative** (§6.1). A closed store (a genesis member's, a member-from-the-start device's, or one
  restored from a closed own-account export) never takes a boundary digest (`acceptView_sound`). So
  `fetched` stays exact for every closed store.
- **Where boundary digests come from.** Only from replies that pass §4.4: solicited, sealed to this
  account, from a responder whose key has not changed since the request. The responder's ACI is
  stored as the voucher. A newcomer cannot check a digest (he has no preimage); a member who lies
  can hide a record from him (incompleteness, attributable to that member, never a leak). An
  import's boundary digests are vouched by the giver.
- **Boundary admission** (round 2, protocol 4). A **catch-up** reply is the responder's whole
  frontier (`Serve.serve_boundary`: each boundary entry is linked by a served record or is a
  responder head), so in catch-up mode `ACCEPT_VIEW` keeps every boundary entry. A **per-digest**
  reply answers digests asked for by name, and a digest that nothing links would become a head
  that never goes away (`LINKABLE` never links a boundary digest), so the newcomer's compare code
  would never match again (round 2 showed this). So in per-digest mode a new boundary digest is
  kept only if it is stored or a stored record links it, counting records accepted in the same
  request; the host passes the pending records that wait for it (§4.4), so they resolve through it
  in one request. Otherwise it is dropped (`IGNORED`) and stays unknown; a pending record that
  needs it gets `MISSING` again. Proved: `acceptView_boundary_linked` (per-digest: every boundary
  digest the request adds is stored or linked by a stored record) and `acceptView_heads`,
  `run_acceptView_heads` (per-digest: every head afterwards is a stored record or was a head
  before).
- **What is not true:** "every boundary digest of a relative store is linked by a stored record".
  Counterexample: a newcomer catches up when nothing was posted since the add. The reply is just
  `[boundary H]`, H the responder's head; the newcomer holds no record, and H must be his head, or
  his compare code would not equal the responder's.
- **Containment: a relative store's own records link only what a live record vouches for.** In a
  relative store, `COMMIT` links only `LINKABLE`'s digests: the heads that are held records with
  provenance `live` (its own included) or author copy (`run_linkable`). Boundary digests and relayed
  or structure-only heads are left for others to link; compare codes still use all heads. Reason: a
  digest nobody holds a preimage for (a phantom), once linked by the holder, would leave every later
  record of his unresolvable at every member. Under this rule a phantom can reach his records only
  through a record its author sent live or as author copy, which is attributable to that author. A
  closed store keeps A7's rule (links = heads): every link it holds resolves.

### 6.3 What he learns

- the records sent to him, with content;
- `after` structures (§6.4);
- opaque digests for the older records those link to directly, and for older heads.

The digests are pseudorandom, because the commitment is salted. No former member's ACI is shown,
including in quotes and in messages that point at an older message (§8.3), with one known gap: votes
on a poll sent before the add. The count of boundary digests is visible; Signal already reveals a
similar count through the iteration in a newcomer's sender-key distribution message.

### 6.4 `after` entries

A member whose client had not yet applied the add can write a message that links a message sent
to the newcomer but is not itself sent to him. That message reaches him as an `after` entry:
author and links, no content. It is needed to keep the newcomer's heads equal to the responder's.
Nothing rejects the writer: there is no revision-order check. Honest races cause this; a server
that delays the add in one author's view, which catch-up being best effort allows, prolongs it.
Metadata only.

### 6.5 Removal and re-add

- **Removal.** Signal resets the author's sender key at its next normal group send, in the author's
  view. A removed member is not in later audiences, and responders answer current members only.
- **Re-add.** Desktop archives the old store (it stays readable in the UI) and opens a new relative
  store. A catch-up request carries `since` = the old heads ∪ its pending digests ∪ digests it
  knows are referenced but missing; a per-digest request carries the accepted heads. `SERVE` leaves
  out of `vis` what `since` reaches, so the messages written while he was away come back as
  digests, not as `after` structures. Content stays per message: he gets content from both
  intervals that he was sent, and none from the gap. A per-digest repair of a message he was sent
  and missed returns its content whatever `since` says.
- **Responders contribute `since`.** Each responder records, per account, its own heads when it saw
  that account removed in a Signal-authenticated group update (sent by the remover through Signal).
  `SERVE` joins them with the request's `since`. Joining only shrinks `vis`, so it is always safe.
  It covers a requester whose client never saw the removal (the server can hide it, since log
  changes are unsigned), a device of his with no archive, and a request with no `since`.
- **Other devices.** Replies are sealed to the account's identity key, so every device of the
  account can open them; only the requesting device accepts (request id). The account's effective
  `since` is the smallest of its devices', which responder `since` corrects.
- **Residual.** If the server hides the removal from every responder as well, gap structure
  (authors, links) can reach him. Metadata, never content. If it hides the removal from one
  author, that author still seats him: Signal delivers her message to him live, and after a
  re-add every member re-serves it, since its audience seats him. This is the author's-view rule
  (§8.1), shared with Signal; round 2 tested it (§12.3).

### 6.6 Other devices of the same account

Entitlement is per account, and the seal is to the account's identity key, which a linked Desktop
receives at provisioning. So any device of the account, including one linked later or one whose
history the user deleted, can pull what its account was sent from other members, at any time,
for as long as they keep it. This is broader than link & sync (a one-time transfer chosen on the
primary), though it stays inside R1: content goes only to the account it was sent to. Kept by
user decision (§12.2). That device still cannot decrypt old sender-key messages.

### 6.7 Compare codes

By `served_heads'` (§7), a member who has caught up from any responder, absolute or relative,
holds exactly that responder's heads; for the running code, `Serve.serve_heads` and
`Serve.Rel.serve_heads_code`. `agree_rel` then compares his view with any closed store, and
`agree_rel'` with a relative one. Later per-digest replies add no head that is not a stored record
(`run_acceptView_heads`, §6.2). Compare codes between old and new members match.

## 7. What is proved

Two kinds of theorem. **Running-code theorems** are about the functions `zrdtd` runs; they are
the ones that stop a leak caused by a bug. **Spec theorems** are about the abstract model
(`Crdt/Merkle`) and say what a store means. Everything in §7.1 to §7.3 is proved: no `sorry`,
`admit` or `native_decide`, and the axioms are only `propext`, `Classical.choice` and
`Quot.sound`. The axiom gate (`Test/Axioms.lean`, `lake exe axiom_check`) pins them for the main
theorems. What is still open is in §7.5.

### 7.1 Running code (`core/`, Mathlib-free)

**The rule: `core/Zrdt/Serve.lean`.** `Serve.serve` takes a `RawStore`, so one set of theorems
covers closed and relative responders. It is the round-1 scratch, ported without the sent-to path
(greenfield), so each statement is the scratch's without that case: stronger.

- **`serve_content`.** Every opening in a reply opens a stored record, and its own committed
  audience seats the requester's ACI with the tag of the key passed to `SERVE`.
  ```lean
  theorem serve_content (he : Entry.addressed r o ac ∈ serve c me held q) :
      ∃ d : Digest, c.map[d]? = some r ∧
        ∀ op, o = some op → openingMatches r.group r.author r.commit op = true ∧
          ∃ aud, audienceOf op = some aud ∧ seats aud q.aci q.key = true
  ```
  It does not mention `zrdtd`'s audience table, `since`, the responder's provenance, or any host
  flag, so no stale cache or host bug can widen it.
- **`serve_content_complete`.** The converse: every held opening that `serveOpening` accepts (it
  opens its stored record, its audience seats `q`, and it passes the export and strict checks) is
  in the reply (in a catch-up when `since` does not reach it, in a per-digest repair when wanted).
  The two together say that the content of a reply is exactly that set; earlier drafts called the
  pair `serve_content_exact`, which is not a separate theorem. **`q.key` is
  server-influenceable** (TOFU), so the statement alone does not stop a key swap; the seal does
  (§4.3), and `run_serve_content` ties the seal to the same key.
- **`serve_authorCopy`**: an author-copy entry is a stored record the responder wrote, holds
  `live`, and has not disowned. **`serve_strict`**: in strict mode every opening is in an
  author-copy entry. **`serve_export`**: in an export no opening is ephemeral (field 5 or 14).
- **`serve_after`**: an `after` entry is a stored record in the walk back from the `vis` records;
  with `mem_reachersOf` (`ClassifyFast.lean`) it reaches a record sent to the requester that
  `since` does not reach.
- **`serve_boundary`**: a boundary digest is a stored record outside that walk, and if the
  requester is entitled to it, the request is a catch-up whose `since` reaches it; or it is a
  digest of the responder's own boundary. This is the "no hidden hole" statement.
- **`audience_bound`**: two openings that both match one commit have the same audience, or
  SHA-256 has a collision.
- **`parseAudience_writeAudience`**, **`valid_of_parseAudience`**, **`audienceOf_valid`** (round
  2): every well-formed audience reads back, and every audience `zrdtd` reads is well-formed.

**The frame ops: `core/Zrdt/Proto.lean`** (`run` is what `zrdtd` executes).

- **`run_serve_content`**: `serve_content` for the op `SERVE`; also nothing changes, and the reply
  header carries `q.aci`, `keyTag q.key` and the request id. The send wrapper takes the
  destination and the seal key from the header.
- **The audience on accept** (the plan's `accept_audience`, proved as these theorems):
  `accept_accepted` (an `ACCEPT` that says `OK` had a matching opening, and its audience is
  recorded under the record's digest); `accept_refused` (a reply with an empty body leaves the
  table unchanged and is `NO_CHAT`, `BAD_OPENING` or `NO_AUDIENCE`, each with its reason);
  `acceptRecord_accepted` (the same for `ACCEPT_RECORD` with an opening); `checkEntry_record` with
  `acceptView_audiences` (`ACCEPT_VIEW` records only the audience of a matching opening, for a
  stored record).
- **`ACCEPT_VIEW`**: `acceptView_sound` (kind and chat stay, so a closed store takes no boundary
  digest; nothing stored is lost; every new record is that of an entry that passed its checks;
  every new boundary digest is an entry's, vouched by the voucher); `acceptView_built` (the store
  stays correct relative to its boundary); `acceptView_accepted` (`OK` for a record only if it is
  stored); `acceptView_boundary_linked`, `acceptView_heads`, `run_acceptView_heads` (per-digest
  mode adds no stray head, §6.2); `run_acceptView`.
- **Other ops**: `run_merge_audiences` (`MERGE` keeps every recorded audience and records the
  blob's for stored records that had none); `run_audience` (`AUDIENCE`'s value parses);
  `run_addressed`; `run_linkable` (§6.2 containment); `run_newRelative`; `commit_openingMatches`.

**The stores: `core/Zrdt/RelStore.lean`, `ChatStore.lean`.** `rawAcceptRel_built`,
`rawAcceptRel_accepted`, `rawAcceptRel_missing`, `rawAcceptRel_unchanged`; `rawAcceptRel_empty` and
`builtRel_empty_iff` (with an empty boundary, exactly the closed code and invariant);
`RelStore.acceptAll_sound`; `load_ok`, `load_complete`, `load_reopens`; `linkable_sub`; `prune_spec`
(the per-digest drop keeps the store correct and keeps only old, stored or linked digests);
`ChatStore.encode_reopens` and `decodeChat_encodeChat` (a `zrdtS3` blob reopens as exactly its
store, boundary and audiences; since round 2 with no assumption); `mergeAudiences_spec`.

**Tests.** `#guard`s in `Serve.lean`, ported from the scratch: a pre-join record goes to Bob as a
boundary digest only; Carol's stale-view record goes as `after`; its author gets the content under
her own key; an opening whose audience was rewritten to add Bob fails `openingMatches` and is never
served; a requester with a changed key gets no content; an author with a changed key gets none of
its own records (no author shortcut); a blocked member with the zero tag gets nothing; only the
responder's own live records are author copies, and a disowned forgery in its name is not; an
export refuses a disappearing message that a relay carries; a re-added member with `since` gets the
gap as digests and without it as `after`; a per-digest repair returns content whatever `since`
says, and a gap record only as a digest; five crawl shapes of `since` and `wanted` never return the
pre-join record's content or structure; the **H3 regression** (v1's rule `revision ≥ joinRev`
releases Carol's revision-8 record when the server says Bob joined at 5, and `serve` does not); a
responder serves its own boundary digests. Added in the port: an opening with no field 201 goes to
no one, its author included; in strict mode a relay carries no content and the author's own reply
does. `vectors/vectors.json` (7 sessions: `tour`, `tooLarge`, `acceptRecord`, `join`, `view`,
`boundary`, `fuzz`) runs against `zrdtd` (`vectors/zrdtd_client.py`) and, byte for byte, against
the fork's TypeScript stub. The `boundary` session reproduces round 2's stray head under the
protocol-3 rule and shows it gone; the join and view steps build Alice's export for Bob and import
it into a new relative store.

**Satisfiable and rejecting.** `Serve.Examples.self_served` instantiates the main `SERVE`
theorems with every hypothesis discharged. Two examples prove that a reply giving Bob the pre-join
opening, or Bob under a swapped key one of Alice's records, violates `serve_content`'s conclusion
(`ContentOk`). `Crdt/Merkle/ServeExamples.lean` gives `serve_after` and `serve_boundary` real
inputs without running `serve` in the kernel (`Serve.Examples.reply_after`,
`Serve.Rel.Examples.reply_boundary`).

### 7.2 Spec: `Crdt/Merkle/Rel.lean` and the bridge

`Crdt/Merkle/Rel.lean` is the scratch `docs/join-v2/Rel.lean` ported onto the spec's `Record` and
`Store`. It states the versions for a responder with its own boundary `BS` (primed); with
`BS = ∅` they say what the closed versions say (`headsRel_empty`, `closedRel_empty_iff`).

- **`agree_rel'`.** If a view (full records `F`, boundary `B`) has the same heads as a store
  `(S, BS)` closed relative to `BS`, every reachable digest is a digest of `S` whose view records
  are all in `S`, or a digest only in `BS` that the view holds no record for, or two records
  collide. **Nothing is assumed about `B`**: this is why v1's revision check and H2's two-level
  hash are not needed. Hypothesis: the view holds no full record for a digest the responder has
  only as boundary (true of every served view). For a closed responder this is
  `CheckedStore.agree_rel` (§7.3).
- **`served_heads'`.** The view a responder serves for any predicate `vis` (full records: those
  reaching a `vis` record; boundary: the other digests of its view linked by them, or heads,
  including its own boundary digests, `servedB'`) has exactly the responder's heads. No collision
  hypothesis.
- **`served_closed'`, `served_tight'`**: the served view is closed relative to its boundary, and
  tight when the store is. **`served_boundary'`**: a served boundary digest is one the responder
  knows, and from it no `vis` record is reachable. **`newcomer_agree'`**: a tight view with the
  served heads holds only records of the responder's store, or two records collide.
- **Limits**, checked by `decide`: `after_record_served`, `phantom_boundary_indistinguishable`,
  `below_boundary_not_vouched`, and `Breaker2.relative_responder_not_closed` (serving only stored
  records from a relative responder gives a view that is not closed; `relative_responder_closed'`
  shows the responder's own boundary closes it).
- **Bridge `serve_abs`**: `Serve.serve_abs` (`ServeAbs.lean`, closed responder) and
  `Serve.Rel.serve_abs` (`ServeAbsRel.lean`, relative responder). The records and boundary of
  `serve`'s catch-up reply are `servedF` and `servedB'` for `vis r := entitled q r ∧ ¬ reachable
  from since`, with `BS` = the responder's boundary. Records whose audience the responder does not
  hold are covered: they are boundary digests when linked by a served record, or heads. From it:
  `serve_heads`, `serve_closed`, `serve_tight`, `serve_boundary_spec`, `serve_after_reaches`,
  `replyRecords_subset`, in both files, and `Serve.Rel.serve_heads_code` (the heads a newcomer
  gets are the responder's `HEADS`).
- **A store with a boundary in the model**: `RelSpec.lean` (`acceptRel`, `AcceptBuiltRel`,
  `buildRetryRel`, `reach_transfer`, and the cycle counterexample `promoted_cycle`),
  `RelRefine.lean` (each `RelStore` operation seen in the model), `ClassifyRel.lean`
  (`classifyRaw` computes the spec's status on any raw store whose records sit under their digests
  and have no cycle).

### 7.3 Advertised theorems: `Crdt/Merkle/Api.lean`

27 statements, listed in `comparator.json` and restated word for word in
`Comparator/Challenge.lean`.

- **The 11 of before**, for a closed store (`CheckedStore.fetched`, `no_collision`, `agree`,
  `abs_accept`, `abs_merge`, `open_iff`, `salvage_spec`, `encode_open`, `confirmed`,
  `classify_spec`, and `encode_injective`). Unchanged.
- **New for joining** (Part 4): `CheckedStore.agree_rel` (`agree_rel'` for the shipped store,
  the responder's boundary `BS` an argument), `CheckedStore.serve_content` and
  `CheckedStore.serve_content_complete`. They are stated over `abs c` like the others; the
  running-code names `Serve.serve_content` and `Serve.serve_content_complete` are in core, which
  the challenge imports, so it cannot restate them under those names.
- **The 11 for a store with a boundary** (Part 5, the same names under `RelStore`: `fetched`,
  `no_collision`, `agree`, `abs_accept`, `abs_merge`, `open_iff`, `salvage_spec`, `encode_open`,
  `confirmed`, `classify_spec`). `encode_injective` is about one record, so no boundary enters,
  and it holds as stated. With an empty boundary each says what the closed statement says
  (examples in Part 5). Two hypotheses are new, each with a checked counterexample: `agree` needs
  that neither store holds a record whose digest the other has only as a boundary digest
  (`below_boundary_not_vouched`); `fetched`, `agree` and `classify_spec` need no cycle
  (`Acyclic`), because a promoted record can close a cycle without a collision (`promoted_cycle`,
  `promoted_cycle_not_tight`, `RelSpec.lean`; for SHA-256 this needs a record whose digest was
  written into a record its own digest depends on). `BuiltRel.acyclic_of_unpromoted` gives it
  when no record was promoted. `confirmed` holds up to the sender's boundary. `CLASSIFY` on a
  relative store is `classifyRaw`, and `RelStore.classify_spec` rests on `ClassifyRel.lean`.
- **The three join statements for a responder with a boundary** (a former newcomer re-serves):
  `RelStore.agree_rel` (its own boundary as `BS`), `RelStore.serve_content` and
  `RelStore.serve_content_complete`, with examples on Bob's relative store and on a store holding
  Alice's message over the boundary digest of `a1`.

### 7.4 Deniability

No theorem is needed. `COMMIT`, `encode`, `AUDIENCE` and `SERVE` take no secret key: the key tag
hashes a public key. Anyone who holds the content, the nonce, the links and the public keys
computes the same bytes. The seal uses a fresh ephemeral key and the requester's public key and
authenticates nothing. Deniability of live messages and pairwise messages is libsignal's, in the
trusted base.

**One limit, stated (round 1).** A compare or checkpoint code is the set of heads; through the
commits it pins every message's content. Reading one aloud on a recorded channel ties the speaker
to that transcript, much as a signature would. Compare codes inside Signal, where the channel is
deniable. Short SAS-style codes, keyed by nonces exchanged in-band and deleted afterwards, would
remove the limit (later option, §10.3).

### 7.5 What is still open

- **Comparator** has not been run over the 27 statements (it needs about 63 GB of RAM). It is the
  final step, with the user's approval. `lake build` and `lake exe axiom_check` pass.
- `accept_refused` covers `ACCEPT` only. For `ACCEPT_RECORD`, "a refusal changes nothing" holds
  in the code but is not stated as a theorem.
- The importer's seat check on exports is host code (§4.5). An `ACCEPT_VIEW` import mode that
  checks it in `zrdtd`, with a theorem, is an optional follow-up.
- Trusted, as before: the protobuf scan of field 201 (`fieldValue`, `audienceOf`), like the
  commitment's scan. The host code of §8.2, §8.3 and §4.4 (the seal, the reply checks, the target
  and quote rules, the export seat check) is tested, not proved (§12.4).

## 8. Why no pre-join data reaches a newcomer

### 8.1 Against a lying server

| Attack | Why it fails |
|---|---|
| Replay old group envelopes to the newcomer. | Signal: sealed sender v2 gives him no per-recipient slice of an earlier message; pairwise sessions carry no earlier sender key; his sender-key state starts at the current iteration ("old counter"). |
| Send a retry request in his name for old timestamps. | Signal: the sendLog has no row for him (`handleRetry.preload.ts:196-202`). |
| H3: tell an offline responder that Bob joined at revision 5 when he joined at 9; Carol wrote at revision 8. | `SERVE` reads no revision. Carol's opening commits an audience without Bob, so he gets a boundary digest. |
| Forge a zrdt request in a member's name. | Requests are Signal messages, authenticated to the identity key the responder currently trusts (TOFU; accepted on receive, trusted for sending after 5 s). A swapped key is the next row. |
| Swap a member's identity key and request his history. | The tag in each audience is for the key the author held. `SERVE` seats only a requester whose current key has that tag, and the reply is sealed to that key, so a session Signal re-targets later (5 s trust, 409/410 re-fetch) carries bytes the swapped key cannot open. Residual, Signal's own: a key swapped before the author froze the message; Signal itself sent that message to it. |
| Swap a member's key and send a newcomer an unsolicited reply with phantom digests or fake `after` records. | `ACCEPT_VIEW` takes only solicited replies sealed to the newcomer, from a responder whose key has not changed since the request. A relative store's own records never link a boundary digest or a relayed head (§6.2), so a phantom cannot stall his later records. Closed stores never take boundary digests. Residual, Signal's own: a key substituted on first contact impersonates that member, in Signal too. |
| Show a responder that a removed member is still a member. | He gets only content he was already sent. Gap structure only if the server also hides the removal from that responder (§6.5). |
| Hide a removal and re-add from the member's own client. | Responders join their own `since` (§6.5). |
| Show an author an early promotion of an invited or requesting account. | Signal itself then delivers that message live to him. Access follows the author's own membership view at enqueue and freeze, exactly as Signal's live delivery does. Optional later fix: the `ATTESTED` gate (§10.3). |
| Mark the newcomer unregistered at an author (`uuids404`). | He gets the zero tag: no zrdt content, as no Signal delivery. The quote rule checks seats, so no quote reaches him either (§8.3). Denial of service. |
| Fail an author's key fetch at freeze. | Freeze waits and retries, as the send does; the zero tag only for a 404. |
| Drop or delay anything. | Denial of service, a non-goal. Gaps show (A12). |

### 8.2 Against a buggy responder

Whatever the host passes to `SERVE` (any opening, any cached audience, any `since`, any provenance
or classification it expected), `serve_content` holds: an opening leaves only if it opens a stored
record and its own committed audience seats the requester's ACI and key. A wrong opening fails
`openingMatches`. A stale cache affects structure entries only. What remains a host duty:
- pass the Signal-authenticated requester ACI and the identity key Desktop holds for him; the send
  wrapper takes the destination and the seal key from the reply header, so a wrong destination
  receives bytes it cannot open;
- send no opening outside a sealed `SERVE` reply (one constructor, plus a lint rule), and never
  re-send the sendLog on a zrdt request;
- pass this device's true `live` set and disown set (they decide author copies, and so what a
  strict responder releases);
- on the author's side, build the audience from the enqueue snapshot and the freeze-time members,
  never from the members at a later send. A TypeScript test pins "seats ⊆ recipients at enqueue ∪
  {author}" and "recipients at every attempt ⊆ audience ⊆ `membersV2` at enqueue ∪ {author}".

### 8.3 Signal paths the fork closes

- **Edits, and every message that points at a target** (the target rule). An edit of message `r`
  goes to `r`'s seats intersected with the current recipients, not to
  `conversation.getRecipients()` (`sendEditedMessage.preload.ts:135-139`). Round 2 extended this to
  every message that names a target's author and sent timestamp: reactions, pins and unpins,
  delete-for-everyone (decided at enqueue, while the target still holds its opening), poll votes
  and poll ends. Each goes only to the target's seats ∩ the current recipients when the target
  has a committed audience (`getZrdtEditRecipients`, `splitZrdtTargetConversationIds`,
  `ts/zrdt/quote.preload.ts`). So a newcomer never learns the author or time of a message he was
  not sent. A message sent over the cap has no record and no audience; messages that point at it
  go the stock way. **Known gap:** a poll is not a record, so it has no audience, and a vote on a
  poll sent before the add still reaches the newcomer (metadata).
- **Quotes.** The rule runs in one place: on the return value of `uploadMessageQuote` in
  `sendNormalMessage` (`jobs/helpers/sendNormalMessage.preload.ts:844-990`), on every attempt. That
  function builds the wire quote for sends, edits and manual retries alike. `makeQuote`, which runs
  when Reply is clicked or a draft is restored, is left alone, and so is the local `quote`
  attribute (the author's own UI).
  - For a quote of `p` inside message `n`: keep the text, body ranges and thumbnails only if every
    account that can receive `n`'s content (this attempt's recipients, and `n`'s seats in field
    201) is seated in `p`'s committed audience, by ACI. If the author holds no audience for `p`,
    strip.
  - A stripped quote carries no text, body ranges, attachments, id or author. It carries `p`'s
    record digest in a new `Quote` field 201 instead, so the newcomer learns neither the
    pre-join timestamp nor a former member's ACI. Fork receivers that hold `p` refill the quote
    from their own copy (`messages/copyQuote.preload.ts:47-150`); a newcomer sees "original not
    found"; stock clients see a quote without an original.
  - TypeScript tests: a reply drafted before an add and sent after it; an edit of a message whose
    quote was stripped; a blocked member and a member seen as unregistered among the recipients;
    the target rule (`quote_test`). The smoke (beat 6) checks that a reaction and a pin on a
    pre-join message, sent after the add, never reach the newcomer.
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
| A newcomer cannot read older group ciphertext | Signal | sealed sender v2's per-recipient encapsulation and pairwise sessions; the sender-key forward ratchet |
| Retries go only to original addressees | Signal | sendLog by recipient (24 h), to the key current then |
| No history for new members | Signal | none exists |
| Live messages authenticated, deniably to outsiders | Signal | sealed-sender MACs; sender-key signatures (verifiable inside the group by every chain holder, kept only in flight) |
| History between one account's devices | Signal precedent | link & sync; zrdt own-account export. zrdt's re-serving to any device of the account is broader (§6.6) |
| zrdt relays, catch-up and exports send content only to seated accounts | **zrdt** | field 201 + `SERVE` (closes gap 1) |
| That content is readable only under the key the author addressed | **zrdt, from Signal's primitives** | key tag + the seal: sealed sender v1's ephemeral-key layer with libsignal `agree`, HKDF, AES-GCM-SIV (closes gap 5) |
| Edits and quotes carry no older content to newcomers, and reactions, pins, deletes and votes no older metadata | **fork rule** | §8.3 (closes gap 2; votes on older polls excepted) |
| Access follows the author's own membership view at enqueue and freeze, as Signal's live delivery does, and no other server-asserted fact | **zrdt** | no revision read; the author's frozen audience; responder `since` only shrinks (closes gap 3) |
| Older links resolve without content; heads still compare, across generations | **zrdt** | relative store, boundary digests vouched by named members and never linked by the holder, `served_heads'` (closes gap 4) |
| A relayed copy shown as the author's | **Signal channel + zrdt rule** | the author's own sealed `SERVE` reply, author copy only for its own live, undisowned records; otherwise A8 confirmation |

**Trusted** (beyond A12: the Lean compiler and runtime, the frame codec and protobuf scan, the
TypeScript client, SHA-256 collision resistance):
- **libsignal:** sealed sender v2 and pairwise sessions; the forward ratchet; the deniability of
  sealed-sender MACs; `PrivateKey.agree`, HKDF and AES-256-GCM-SIV, used by the seal.
- **Signal's server, for one thing:** the member list an author's client sees when it composes and
  freezes a message, including who it shows as unregistered. Signal already trusts the server for
  exactly this. The server is not trusted for revisions, join revisions, the change log, or
  anyone's join point.
- **Identity keys:** Signal's trust-on-first-use and safety numbers. The key tag and the seal
  inherit them: a key substituted before the author froze a message, or on first contact, is
  Signal's exposure; after the check zrdt adds none.
- **New small host code:** reading field 201 (`audienceOf`, `parseAddressees`) joins the unproved
  protobuf scan; the seal module and `sendZrdtServed`, with a test vector; the solicited-reply
  check; the export files and the importer's seat check (§4.5).
- **Host duties:** §8.2; the audience snapshot; `since` on both sides; passing only replies that
  pass §4.4 to `ACCEPT_VIEW`, with the request's mode and the pending records; not applying
  side-effect fields of late copies; the edit, target and quote rules; `MERGE` only of the
  account's own export; the per-group strict setting; running the Lean `zrdtd` (the TypeScript
  stub runs only under tests, or with an explicit `ZRDT_ALLOW_STUB=1`).
- **Members:** honest or attributable. Boundary digests are vouched by named members (§6.2).

## 10. Wire, frame ops, staging

### 10.1 Wire

```proto
message DataMessage { ...; optional bytes zrdtAudience = 201; }      // §3.2; inside the commitment
message Quote { ...; optional bytes zrdtRef = 201; }                 // §8.3; a stripped quote's target digest
message ZrdtServeRequest { bytes groupId = 1; bytes requestId = 2;   // 16 random bytes
                           repeated bytes digests = 3; repeated bytes since = 4;
                           optional bool catchup = 5; }
message ZrdtServed { bytes groupId = 1; bytes header = 2;            // requester aci ‖ key tag ‖ request id
                     bytes ephemeralKey = 3; bytes sealed = 4; }     // SERVE's entries, sealed (§4.3)
message Content { oneof content { ...; ZrdtServed zrdtServed = 203;
                                       ZrdtServeRequest zrdtServeRequest = 204; } }
```

`ZrdtResendRequest` (Content 200) and `ZrdtResend` (201) are removed: neither sent nor parsed
(greenfield, §3.3), and their numbers are not reused. `ZrdtNotFound` (202) stays.

### 10.2 Frame ops (protocol 4)

The header of `core/Zrdt/Proto.lean` fixes every byte and is authoritative; this table lists what
JOIN added or changed. Field types are the header's: `digests` is a `u32` count and that many
digests, `flag` a `u8` 0 or 1, `key` 33 bytes, `rid` 16 bytes, `opening` a `u32` length and bytes.

| Op | Name | Request | Reply |
|---|---|---|---|
| `0x07` | `ACCEPT` (changed) | chat ‖ parts ‖ `opening` (always; no flag) | `OK` digest ‖ encoding; `MISSING`, `COLLISION`, `WRONG_CHAT`, `TOO_LARGE`, `NO_CHAT`, `BAD_OPENING`, `NO_AUDIENCE` |
| `0x10` | `ACCEPT_RECORD` (changed) | chat ‖ record (`bytes`) ‖ `u8` (1: an `opening` follows) | as `ACCEPT`, plus `MALFORMED`; without an opening the record is stored as structure, no audience |
| `0x11` | `AUDIENCE` | `u32` n ‖ n × (aci ‖ `u8` hasKey ‖ key if hasKey) | `OK` field-201 value; `TOO_LARGE` over 256; `MALFORMED` (no members, an ACI twice) |
| `0x12` | `SERVE` | chat ‖ own aci ‖ requester aci ‖ requester key ‖ rid ‖ since ‖ responder since ‖ `u8` mode (0 catch-up, 1 per-digest) ‖ wanted (mode 1 only) ‖ export `flag` ‖ strict `flag` ‖ live ‖ disown ‖ `u32` n ‖ n × (digest ‖ opening) | `OK` header (requester aci ‖ key tag ‖ rid: 48 bytes) ‖ `u32` n ‖ entries; `NO_CHAT` |
| `0x13` | `ADDRESSED` | chat ‖ aci ‖ key | `OK` digests whose recorded audience seats them; `NO_CHAT` |
| `0x14` | `ACCEPT_VIEW` | chat ‖ voucher aci ‖ import `flag` ‖ `u8` mode (0 catch-up, 1 per-digest) ‖ entries ‖ pending | `OK` `u32` n ‖ one result per entry, then per pending entry; `NO_CHAT` |
| `0x15` | `LINKABLE` | chat ‖ live | `OK` digests: for a relative store the heads that are held records in `live` (the `COMMIT` links, §6.2); for a closed store `HEADS` |
| `0x16` | `NEW_RELATIVE` | chat ‖ group | `OK`: an empty relative store; `CHAT_OPEN` |

- **Entries** (a `SERVE` reply after its header, and `ACCEPT_VIEW`'s entries and pending): a
  `u32` count, then per entry a kind byte: `0x00` addressed = record (`bytes`) ‖ author-copy
  `flag` ‖ `u8` (1: an `opening` follows); `0x01` after = record (`bytes`); `0x02` boundary =
  digest. The requester passes a reply's unsealed entries to `ACCEPT_VIEW` unchanged.
- **Results** (`ACCEPT_VIEW`): a status byte, then the digest for `OK` (the record's, or the
  boundary digest), the missing `digests` for `MISSING`, the digest for `COLLISION`, otherwise
  nothing.
- **Statuses.** `0x08` `BAD_OPENING` (the opening does not match its record) is A4's, now also
  from `ACCEPT` and in `ACCEPT_VIEW` results. New, all with an empty body: `0x09` `NO_AUDIENCE`
  (the opening matches but holds no single well-formed field 201, §3.2);
  `0x0A` `EPHEMERAL` (an `ACCEPT_VIEW` result in import mode: a disappearing or view-once
  opening); `0x0B` `IGNORED` (an `ACCEPT_VIEW` result: a boundary entry a closed store does not
  take, or one dropped in per-digest mode, §6.2). Every refusal changes nothing.
- **Changed ops.** `OPEN`, `SALVAGE`, `MERGE` and `ENCODE` read and write `zrdtS3` only (§3.3).
  `MERGE` records the blob's audience for each stored record that has none; a recorded audience
  stays. `HEADS` on a relative store lists held digests and boundary digests that no held record
  links; `HAS` and `GET` know stored records only. `VERSION` reports protocol 4.

### 10.3 Staging

Greenfield (§3.3) leaves three stages, each built on the one before. They replace v2's phases;
the former Phase 3 was dropped in round 1 (§11). **All three are built on `join`**, with the
round-2 fixes (§12.3). The demo build has none of them; its leak stays latent in a static group.

- **Stage 1, core ops** (Lean, `zrdtd`). `audienceOf` and `AUDIENCE`; `ACCEPT` with the opening
  and `NO_AUDIENCE`; the audience table in `zrdtS3` (boundary section empty); `SERVE` with the
  export and strict flags; `ADDRESSED`; `ACCEPT_VIEW` for a closed store, which ignores boundary
  entries. The §7.1 theorems other than the relative store's, and vectors for the new ops.
- **Stage 2, the fork.** Field 201 at freeze (§4.1) and `ACCEPT` with the opening on receive; the
  seal and `sendZrdtServed`; request ids and the §4.4 checks; `ZrdtServeRequest` and `ZrdtServed`
  (Content 204, 203), with 200 and 201 removed; `resend.preload.ts` calls `SERVE`, and the old
  member check and the zrdt-triggered sendLog re-send are deleted; the edit and quote rules; exports
  through `SERVE` with the export flag; the per-group strict setting, off by default. A stage-2
  store is closed, so a newcomer's pre-join links stay pending, as today. From this stage on,
  membership changes do not leak content.
- **Stage 3, the relative store.** `RelStore` and the boundary in `zrdtS3`; `NEW_RELATIVE`;
  `ACCEPT_VIEW` for a relative store; `LINKABLE`; the `Rel.lean` port and the restated advertised
  theorems (§7.2, §7.3); catch-up for any device without a store; archive and `since` on re-add;
  responder `since` from Signal-authenticated removals; the boundary row and the "content not
  available" labels in the UI.
- **Later, optional:** sharing by choice (§8.4); short SAS-style compare codes (§7.4); an
  `ATTESTED` gate, where an author seats only members whose add, promotion or approval it saw in a
  Signal-authenticated group-update message from the actor, or performed itself. That gate would
  close the early-promotion residual of §8.1 at a cost in liveness.

## 10a. Designated-verifier signatures: a signature that can't be used against you

**The principle.** Signal's authentication is deliberately deniable: a message convinces the person
who received it that you sent it, and nobody else. Anything zrdt adds must keep that. In one line:
if you need a signature from me, you can check it, and you can't use it against me.

**v2 adds no signature and no MAC.** Its one new use of a key is the seal (§4.3): a fresh
ephemeral key per reply, agreed with the requester's public identity key, for confidentiality
only. It authenticates nothing, so it can be used against no one. Every authentication is Signal's:

| What is authenticated | How | Why it is deniable |
|---|---|---|
| A live message and its links | sealed-sender v1 static-key MAC, v2 per-recipient tag | both are MACs from identity-key agreement; the recipient could compute them |
| The author's own re-send (author copy) | a 1:1 Signal message from the author, carrying a sealed `SERVE` reply | pairwise, designated-verifier; the seal adds no authenticator |
| A relayed copy | not authenticated by itself; `relayed(by)` until the author's own live messages confirm it (A8) | it proves nothing to anyone |

The record, the commit and the key tags are hashes that anyone holding the inputs recomputes. They
are no evidence of authorship. Four things would break deniability, and v2 does none of them:
signatures under identity keys; treating the server-signed sealed-sender certificate as bound to
content; **keeping sender-key messages beyond flight** (any holder of the author's chain can verify
them, and their plaintext includes field 200, so one kept message commits the author to the hashes
of what she had seen); and **broadcasting per-member tags** (below).

**Why no tag scheme (E1, dropped in round 1).** v2 had kept, as an optional extension, sealed
sender v2's per-recipient tag with zrdt's own label: the author computes
`tag_X = HMAC(HKDF(X25519(a, X_pub)), … digest)` for every audience member and broadcasts the list
in field 200. That is not deniable. Every holder Y of the list keeps `tag_X`, a value only the
author or X can compute; a judge with Y's device and X's identity key (seized, or from X
cooperating) checks it and concludes that Y's copy came from the author or X, and Y received it in
the author's message. `reader_can_forge` (`docs/join-v2/Dvs.lean`) proves only that X could have
made the tag; it does not account for an independent holder. Sealed sender v2 avoids this because
the server splits the message and each recipient receives only its own tag. A tag sent only to X,
1:1, adds nothing over the pairwise channel. So no tag construction is kept. (Lesser issues, now
moot: the key bound ACIs but not identity keys, nothing rejected a non-contributory agreement, and
`Dvs.lean`'s `pairKey` did not match the text.) `Dvs.lean` stays only as HMAC and HKDF over the
shipped SHA-256, checked against RFC 4231 and RFC 5869 vectors.

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

- **Review round 2 (2026-11-01, on the built code)** (§12.3). A leak hunt found one content leak,
  through another member's export file, and two metadata leaks; the verifiers found a stray head
  after per-digest repairs and an `ACCEPT` that could skip the opening. Fixes: exports sealed to
  one account and built by `SERVE` for that account (§4.5); the target rule (§8.3); boundary
  admission in per-digest mode (§6.2); `ACCEPT` always takes the opening (§4.2). Protocol 4.
- **User decisions (2026-11-01, after round 1)** (§12.2). Greenfield removed round 1's
  pre-upgrade machinery and made field 201 required.
- **Review round 1 (2026-11-01, three breakers: 1, the malicious server; 2, R1, R2 and
  completeness; 3, the Signal facts and R2).** v2's core held: field 201 is bound by the commitment, `SERVE` gates
  content on the opening's own audience, H3 has nothing to work with, and every crawl attempt by a
  newcomer failed. What broke, and what changed (the full list is §12.1):
  - **The key check was a time-of-check/time-of-use race** (all three breakers). Desktop trusts a
    changed key on receive at once and for sending after 5 s, and re-encrypts on 409/410, so a
    server could have `SERVE` check the real key while the reply was encrypted to its own. Fix:
    seal the reply to the checked key with sealed sender v1's ephemeral-key layer (§4.3), and drop
    the zrdt-triggered sendLog re-send.
  - **Phantom boundary digests** from a key-swapped "member" could stall a newcomer's records at
    every member, and spread as holes. Fix: solicited, sealed replies from an unchanged key only;
    closed stores never take boundary digests; a relative store links only live or author-copy
    heads (§6.2).
  - **Second-generation newcomers could not catch up** from a former newcomer (proved by breaker 2).
    Fix: `SERVE` and `Rel.lean` take the responder's own boundary (`served_heads'`,
    `served_closed'`, `agree_rel'`, all proved).
  - **The author's own reply was always `live`,** so a forgery the author had accepted and
    disowned (A8) reached a newcomer as confirmed. Fix: author copy only for the responder's own
    live, undisowned records (`serve_authorCopy`).
  - **The quote rule ran at Reply-click time** and checked the wrong set, and blocked or
    seen-as-unregistered members were seated, so relays reached accounts Signal skips. Fix: the
    quote rule at `uploadMessageQuote` against seats; the zero tag for members Signal does not send
    to; stripped quotes point by digest (§8.3, §3.2).
  - **Exports dropped A9's exclusions.** Fix: the export flag (`serve_export`).
  - **Phase 3 (forwarding kept sender-key messages) dropped.** A kept sender-key message is a
    signature any chain holder can verify, which fails R2; a genuine one paired with a made-up
    record could launder forged content as `live`; and it consumed message keys. The author's own
    sealed reply gives `live` provenance without it.
  - **E1 (broadcast designated-verifier tags) dropped:** a broadcast tag list is a two-witness proof
    (§10a). This also refutes H1's "deniably".
  - **Overstated claims corrected:** the primary pre-join barrier is SSv2's per-recipient
    encapsulation; removal rotation is view-relative; "Signal-authenticated" means TOFU; per-account
    re-serving is broader than link & sync; sender-key signatures are not deniable inside the
    group; "zrdt never adds anyone to what Signal sent" and "access never depends on a
    server-asserted membership fact" were replaced by "access follows the author's own view at
    enqueue and freeze".
  - **Completeness fixes:** responder `since` (removal hidden from the requester); catch-up for any
    device without a store; per-digest content regardless of `since`; no freeze on a transient
    key-fetch failure; "content not available from X" instead of "not sent to you"; a new request
    Content number. (Round 1 also added an author path for pre-upgrade history, a backfill and an
    add-member gate for mixed versions; the greenfield decision removed them.)
- **v2 (2026-11-01): the author's audience, committed.** Chosen after a review that checked v1's
  Signal facts against source and compared four designs (below).
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
  principle, and the review brief.
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
    (Round 1 adds: the hash check would not have stopped phantom digests, and forwarded sender-key
    messages fail R2.)
  - **Addressee slots:** per-member designated-verifier MACs hashed into the record, so a
    requester proves he was addressed and a newcomer can prove he was not. Not chosen: new
    cryptography on every message, 16 bytes per member in every record, a store refactor to
    leaf-or-full nodes, and a newcomer who sees the whole older message graph. Its MAC
    construction was kept as E1 until round 1 showed broadcast tags are not deniable.
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

The reviewer should try to break the design, then harden it.

### 12.1 Review round 1: dispositions

| Attack (breaker) | Severity | Disposition |
|---|---|---|
| Key check vs. later encryption (TOCTOU) after a key swap (1, 2, 3) | major | fixed: seal to the checked key (§4.3); `serve_content_exact` reworded |
| Phantom boundary digests from a key-swapped "member" (1) | major | fixed: §4.4 checks; closed stores take no boundary; linkable heads (§6.2) |
| Second-generation newcomers cannot catch up (1, 2) | major | fixed: responder boundary in `SERVE` and `Rel.lean`, proved |
| Phase 3 launders forged content as `live` (1, 3) | major | moot: Phase 3 dropped |
| Author's own reply always `live` (2) | major | fixed: `serve_authorCopy` |
| Quote rule at Reply-click time; quotes vs. blocked/unregistered (2, 3) | major | fixed: §8.3 at `uploadMessageQuote`, against seats |
| Blocked and unregistered members seated (2, 3) | major | fixed: zero tag (§3.2) |
| Exports drop A9's exclusions (2) | major | fixed: export flag, `serve_export` |
| Phase 3 retained signatures fail R2 (3) | major | fixed: Phase 3 dropped; claims corrected |
| E1 broadcast tags not deniable (3) | major | fixed: E1 dropped (§10a) |
| Early promotion; overstated "never adds"/"never depends" claims (1) | minor | reworded (§8.1, §9); Signal-inherited; `ATTESTED` later |
| Server hides removal and re-add; `since` gaps; device without archive (1, 2) | minor | fixed: responder `since`, wider requester `since`, catch-up without a store (§6.5) |
| Zero or stale tags from transient failures (1) | minor | fixed: no freeze on transient failure (§4.1) |
| Author shortcut in scratch; zrdt-triggered sendLog path (1, 3) | minor | fixed: shortcut removed (scratch re-proved); sendLog path removed |
| Overstated Signal facts (1, 2, 3) | minor | corrected (§2, §9) |
| Legacy history loses relays; false "not sent to you"; table not backfilled (1, 2) | minor | labels fixed (§4.4); the rest moot: greenfield, no legacy history (§12.2) |
| Export file injects boundary digests (1) | minor | fixed: vouched by the giver, contained (§6.2) |
| Per-account re-serving broader than link & sync (2) | minor | reworded (§6.6); kept by user decision (§12.2) |
| Host sends a reply to the wrong account; `known` bit; tags as metadata (2) | minor | fixed: header-derived destination and seal; `known` dropped; tags documented |
| Stripped quotes leak pre-join timestamp and author (3) | minor | fixed: quote by digest (§8.3) |
| Spoken compare codes bind content (3) | minor | limit stated (§7.4); SAS codes later |
| Mixed versions still leak (3) | minor | moot: greenfield, no older zrdt clients (§3.3, §12.2) |
| R2 residual of kept sender-key blobs (1); H3, field-201 rewrite, envelope replay, forged request, crawls, partial sends (1, 2, 3) | none | fail as written; kept as regression guards (§7.1) |

### 12.2 User decisions (2026-11-01)

Taken by kejace after round 1; they close the questions round 1 left open.

1. **Greenfield.** "We don't have any [pre-upgrade messages], no backwards compatible
   requirements - greenfield project." So there is no `zrdtSentTo` and no author path for records
   without field 201, no handling of legacy Content 200 and 201 messages (removed, §10.1), no
   backfill, no add-member version gate, and no reading of `zrdtS2`. Field 201 is required on
   every record message: `zrdtd` refuses an opening without a valid one with the new status
   `NO_AUDIENCE` (§4.2; chosen over `MALFORMED` so the host can tell why), and `serve_content`
   loses its second case (§7.1). Staging is core ops, then the fork, then the relative store
   (§10.3).
2. **Cap: 256 members** (§3.2). Over it, messages go without zrdt fields.
3. **Strict mode is built, off by default, opt-in per group** (§5, `serve_strict`).
4. **Per-account re-serving is kept** (§6.6): any device of an addressed account may be served
   what that account was sent.
5. **`ACCEPT` always takes the opening** (lead decision in round 2, stated to kejace, not
   objected): every live record has its recorded audience, and a record without content goes in
   with `ACCEPT_RECORD` or `ACCEPT_VIEW` (§4.2).

Open, for kejace: as built (§5), a group's strict opt-in is a setting on each member's client
(Settings → Internal), which applies it to its own replies; nothing on the wire carries it. A switch
that binds every member's client would need a new wire field.

### 12.3 Review round 2: the leak hunt and the verifiers

Round 2 ran against the built code (zrdt `join` at `acbd70a`, fork `join` at `20f625d58`,
protocol 3): a leak hunter attacking a late joiner (Dave) through a mock server, with Dave's phone
as a raw client holding his identity key; a fork verifier (fresh worktree, full smoke); a Lean
verifier. Fixes: zrdt `ed519eb`, `1af7b70` (core, protocol 4), `ab3dfef` to `00c9b96` (proofs);
fork `c06e159e1` to `fc24c77c0`. The fork smoke after the fixes is GO, 73 of 73.

| Finding (who) | Severity | Disposition |
|---|---|---|
| Content leak through another member's export: Dave imported Bob's export and got every pre-join text. The file held the openings as plain JSON, and the import merged Bob's store and kept every opening that matched (leak hunt) | blocker | fixed (§4.5): an own export's content is sealed to the exporter's key and only that account imports it; an export for X is `SERVE` for X, sealed to X's key, imported with `ACCEPT_VIEW`; the importer keeps an opening only if it seats him. Smoke: Bob's own export shows 0 of 12 pre-join texts; Dave's import of it is refused, also with the account field rewritten; Bob's export for Dave gives Dave no pre-join content and no pre-join record |
| `MERGE` of another member's store put pre-join records (authors, links) into the newcomer's relative store (leak hunt) | major | fixed: `MERGE` takes only the account's own export (§4.5); another account's history comes only through `ACCEPT_VIEW` of a `SERVE` reply for that account |
| A reaction to a pre-join message, sent after the add, reached the newcomer with the target's author and sent time; by code reading, pins, deletes and poll votes did the same (leak hunt) | major | fixed: the target rule (§8.3); the smoke checks a reaction and a pin. Left: votes on a poll sent before the add (a poll is not a record) |
| Stray head: a per-digest reply's boundary digest that nothing links became a head for good; Dave's heads `[·3428 ·ad00]`, Alice's `[·ad00]` (fork verifier) | major | fixed in `zrdtd`, protocol 4: boundary admission in per-digest mode and the pending list (§4.4, §6.2); `acceptView_heads`, `acceptView_boundary_linked`; vector session `boundary`; the smoke re-checks heads after the per-digest asks |
| The 11 advertised theorems were not restated for a store with a boundary (Lean verifier) | major | fixed: `Api.lean` Part 5, and the three join statements for a relative responder (§7.3) |
| `ACCEPT` took the opening behind an optional flag, against this document (Lean verifier) | major | decided: `ACCEPT` always takes the opening (§4.2, §12.2); records without content go through `ACCEPT_RECORD` or `ACCEPT_VIEW`; `accept_accepted` strengthened, `accept_refused` new |
| `encode_reopens` assumed that audiences read back; `MERGE` ignored the blob's audiences (Lean verifier) | minor | fixed: `parseAudience_writeAudience` (no assumption left); `run_merge_audiences` |
| No `CLASSIFY` spec on a relative store; `serve_abs` only for a closed responder; no examples for `serve_after` and `serve_boundary` (Lean verifier) | minor | fixed: `RelStore.classify_spec` (`ClassifyRel.lean`); `Serve.Rel.serve_abs`; `ServeExamples.lean` |
| `accept_audience` and `serve_content_exact` named here but absent; this document stale in §0, §3.3, §6.2, §7, §10.2 (Lean verifier) | minor | fixed in this revision: both are groups of theorems (§7.1) |
| Strict mode could not be switched on (fork verifier) | minor | fixed: a per-group checkbox in Settings → Internal, a SignalCI hook, a host test that the setting reaches `SERVE` |
| Without `ZRDT_DAEMON` the app ran the unproved TypeScript stub (both) | minor | fixed: the app needs the Lean `zrdtd`; the stub runs only under tests or `ZRDT_ALLOW_STUB=1`, and `ZRDT_REQUIRE_LEAN=1` refuses it even then |
| Catch-up was triggered by the server's `joinedAtVersion` (fork verifier) | minor | fixed: the trigger is "no store" (§6.1) |
| `DATABASE_SCHEMA.md` stale for migration 1860; the demo doctor sent `ACCEPT` without an opening and read a bare `zrdtS2`; a stale knip tag (fork verifier) | minor | fixed: regenerated; the doctor uses `ACCEPT_RECORD` and reads only `zrdtS3`; tag removed |
| A removal hidden from one author: she keeps seating him, and after a re-add every member re-serves her message (leak hunt) | minor | documented (§6.5); the author's view, shared with Signal; `ATTESTED` later |
| A quote of a message with no audience (a stock client's, or one over the cap) is stripped to an empty quote, so every receiver shows "original not found" (fork verifier) | minor | open, for kejace (§12.4) |
| Not built: a harness key swap answering 409 between `SERVE` and the send, an envelope replay, a `SERVE` differential for relative responders, a remove-and-re-add smoke beat (both) | minor | open (§12.4) |
| About 25 crafted requests from Dave's phone (catch-up and per-digest, crafted `since` and `wanted`, to each message's own author, junk digests, a replayed request id, strict on and off); Signal's retry; quotes; edits; removal and re-add when the removal reached every desktop (leak hunt) | none | held: no pre-join content and no pre-join record came back; pre-join records came only as boundary digests |

### 12.4 Known weak or unproven points

1. **Boundary digests are member-vouched.** A newcomer cannot check them (§6.2), and a hash check
   would not help (H2). The containment rule keeps a phantom out of his own records unless a live
   or author-copy record links it. Since round 2 a per-digest reply cannot add a head; a catch-up
   reply still sets the frontier, vouched by its responder. Decide whether incompleteness
   attributable to a member is acceptable.
2. **The key tag and the seal rest on TOFU.** A key substituted before the author froze a message,
   or on first contact with a newcomer, is Signal's exposure. A member who reinstalls without
   restoring his identity key loses relayed history, as in Signal. Check that the key passed to
   `SERVE` is the one Desktop holds for the requester, and that `sendZrdtServed` seals to it.
3. **Removed member plus a server that lies to responders too** can give him gap structure
   (authors and links, never content). A removal hidden from one author lets her seat him (§6.5).
4. **The author's member view is the server's.** An early promotion faked in one author's view
   makes Signal deliver live to that account, and zrdt follows. The `ATTESTED` gate (§10.3) is the
   fix; it costs liveness.
5. **The relative store re-proofs** (`BuiltRel`, relative accept order, the boundary in `zrdtS3`,
   `linkable_sub`, the 11 advertised theorems) are done: `core/Zrdt/RelStore.lean`,
   `Crdt/Merkle/RelSpec.lean`, `RelRefine.lean`, `ClassifyRel.lean`, `ServeAbsRel.lean`, and
   `Api.lean` Part 5 (§7.3). Check the two new hypotheses (no cycle; no record below the other
   store's boundary) against the counterexamples that force them.
6. **Host code in the trusted base:** the seal module, `sendZrdtServed`, the §4.4 checks, the
   quote and target rules, the export files and the importer's seat check (§4.5). They are tested,
   not proved: unit tests (`seal_test`: a test vector; a reply re-targeted to a swapped key cannot
   be opened; no seal to a key `SERVE` did not check), a randomized stub-versus-`zrdtd`
   comparison (25 seeds), the vectors byte for byte on both backends, and the smoke.
   `@signalapp/libsignal-client` 0.105.4 exposes `hkdf` and `Aes256GcmSiv` to Node, and the seal
   uses them. **Not yet built:** the harness test that swaps the requester's key and answers 409
   between `SERVE` and the send (the mock cannot swap a key); an envelope replay in the mock; a
   `SERVE` comparison for relative responders; a remove-and-re-add smoke beat.
7. **The own export's structure is readable.** Its digests, authors and links stay in the clear
   (no content), because the demo's beat-4 doctor edits them. A reader of someone's own export
   learns that pre-join metadata. Open, for kejace: seal or bind the structure too; beat 4's
   verification failure would then become a plain refusal.
8. **Metadata gaps left:** votes on a poll sent before the add (§8.3). A quote of a message with
   no audience is stripped to an empty quote; open, for kejace: keep its id and author without
   text, which would show the newcomer the timestamp and author of a message he may not have been
   sent.
9. **The demo script on `join`.** `demo/DEMO.md` and `launch.ts` still have Bob hand over his own
   export in beat 5, which `join` now refuses. The smoke uses a five-member roster instead (Erin
   restores in beat 5 from Bob's export for her, Dave joins in beat 6). Open, for kejace: whether
   the script follows. The live demo runs the demo build and is not affected.
10. **The theorems in §7.** Check each statement against the code it names; check that the bridge
    covers `since` and the responder boundary; check that `run_serve_content` ties the header's
    key tag to the key the wrapper seals to. Comparator over the 27 statements is still to run,
    as the final step, with the user's approval (§7.5).

Deliverable: a written verdict with the facts that decide it, and the smallest set of edits to this
document that makes it sound.
