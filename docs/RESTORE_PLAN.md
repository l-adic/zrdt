# RESTORE_PLAN: restore a chat from anyone, verify it with the next live message

Status date: 2026-11-01 (first written 2026-10-31). Follow-up to `PLAN.md`, `PLAN_HUMANS.md` and
`APP.md`. The theorems in the appendix are proved in a scratch file against the 2026-10-31 build
(standard axioms only) and are to be added to `Crdt/Merkle/Chat.lean` in phase A. Nothing here is
in the repository yet.

Review: `docs/review-2026-11-01/` (`REVIEW.md`, `UPDATE-690ae65.md`, `AMENDMENTS.md`). Changes it
caused are marked **[amendment]**; "A8" means section A8 of `AMENDMENTS.md`.

## 1. What this adds

Today's plan recovers a few missing messages by asking the group for them by digest. This
document specs the general case: a device with no history (new device, wiped device, a device
whose stored copy failed `OPEN`) gets the **whole history as a dump from anyone, by any means**,
and verifies it without trusting the source (for the restoring user's own records, see §7). A
member who joined later gets the structure only (§3). **[amendment]**

The source can be a member sending a file over AirDrop, USB or a Signal attachment, or a backup
the user made. A mirror or the server can be a source only if the dump is encrypted (§3). Which
source it is does not matter, because: **[amendment]**

1. On import, `OPEN` checks that the dump's structure is internally consistent (every link
   resolves, every record belongs to this chat), and `COMMIT` checks each content entry against
   its record. This does not show that the dump is complete or current (§2, stage 0).
   **[amendment]**
2. The first live message from any member confirms, exactly, everything that message points at:
   the sender holds those records, record for record. Confirmed means **"held by the sender"**.
   **[amendment]**
3. A record counts as written by its author only when a live message from that author reaches it
   and the author has not disowned it (`authorConfirmed`, A8). A fake that only the dump holds is
   exposed the next time its named author writes. A fake that another member also links live is
   caught only by `disown`, and only for members who receive the author's disowning message live
   (§7). Anything no member's message ever points at stays unconfirmed. **[amendment]**

**The guarantee in plain words.** This holds against the server, and against a dump-giver who
sends no live messages. A member who gives a dump and also links the fakes in their own live
messages makes the fakes "held by" themselves. The named author's client catches that only by
disowning them, and the disown reaches a member with the next live message from that author
(every later message repeats the full disown list) (§2, stage 2; §7). **[amendment]**

**Privacy.** A dump is a file outside Signal's encryption. It leaves out the content of
disappearing, deleted-for-everyone and view-once messages, but the structure of expired messages
(authors, causal shape, count) stays in it. Export needs OS authentication and shows a "do not
share" warning, as Signal's own export does. Stock link-and-sync and Signal backups carry no zrdt
data (§7). **[amendment]**

Signal has no peer history sync: it moves history from a primary phone to its own linked devices,
and it has encrypted backups to its own servers, both same-account; new group members get no
history. Peer sync is unsafe without something like this, because a peer could hand you a doctored
history. With it, any peer will do: the import is checked, and live messages then show which part
each member holds and which part each author wrote. **[amendment]**

## 2. What "correct" means, at each stage

**Stage 0, on import.** `OPEN` (A3) decodes the dump's store blob, recomputes every digest,
checks every record's group and the size limits, and rebuilds the store by accepting each record
once its links are present (one worklist, `acceptAll`, which inserts only through the checked
`accept`). It succeeds iff every record can be accepted (`CheckedStore.open_iff`). The result is a
`CheckedStore`, so every link resolves and every record is reachable from the heads
(`CheckedStore.fetched`). On failure it names the records it could not accept and the missing
digests (`UNVERIFIABLE{unverifiable[], missing[]}`). `SALVAGE` keeps the largest acceptable part
and names the rest (`salvage_maximal`, `CheckedStore.salvage_spec`). Each content entry must open
its record's commitment: `COMMIT(opening) == record.commit` (A9). **[amendment]**

What `OPEN` catches, and what it does not (A10): **[amendment]**

| `OPEN` catches | `OPEN` does not catch |
|---|---|
| removing or altering a record that something links | removing the newest record (a head) |
| a link to nothing | editing a head |
| a record whose group was changed | appending a forged record |
| malformed bytes | a **stale** dump (a prefix) |
| | a dump whose **whole tail was replaced** by a consistent fake |

Everything in the right column is a valid history that ends somewhere; editing a head is a tail
replacement of length one. `withheld_tail_undetectable` and `tail_replaced_passes_open` are this
limit. So passing `OPEN` says the dump is well formed, not that it is genuine. Every record that
an import or `SALVAGE` adds to the store starts `imported` (§3). **[amendment]**

**Stage 1, the first live message from a member.** Signal authenticates the sender, so the
message's links are what that member's client sent: for an honest client, its heads at send time.
Two cases: **[amendment]**

- The links resolve in your store. Then the records reachable from them in your store are,
  record for record, the records reachable from them in the sender's store. Or two records
  collide. (`confirmed_exact`; over the shipped type, `CheckedStore.confirmed`.) This means
  "held by the sender", not "written by their authors". One live message from a member who was
  caught up when sending reaches every genuine record except those written concurrently with it
  (neither reaches the other) or after it. What it does not reach (those records, and fakes)
  keeps its status. A sender who was behind reaches less. **[amendment]**
- Some link does not resolve. `ACCEPT` returns `MISSING{digests}` and leaves the store unchanged
  (`CheckedStore.abs_accept`); the app asks for those digests by resend (§3). Usually the dump was
  stale. A gap is not proof that the server is at fault: a member can link a made-up digest, and
  an offline author gives the same result (A12). **[amendment]**

**Stage 2, what stays unconfirmed, and who wrote what.** Lean's `CLASSIFY` (A8) gives each record
a status, from the store and the host's live facts (which records arrived `live`, from whom, and
their `disown` lists): **[amendment]**

- `unconfirmed`: no member's live record reaches it. These are the newest messages, which will be
  reached shortly, and fakes that only the dump holds: a member's message reaches a record only
  if that member holds it (`reach_implies_held`). A fake that some member links live is held by
  every member who accepted that message; `disown` handles it (below).
- `heldBy(X)`: a live record of member X, who is not the author, reaches it. If several members
  do, `X` is the one with the smallest ACI in byte order, so every device names the same member.
  **[amendment]** (lane T5)
- `confirmedByAuthor`: `authorConfirmed r` holds, that is, some `live` record from `r.author`
  reaches r, and no `live` record from `r.author` lists r in `disown`. By `authorConfirmed_sound`,
  if the author's client is honest (it disowns every accepted record in its own name that it did
  not create), every author-confirmed record attributed to it was created by it, or two records
  collide. This needs the viewer to have received the disowning message live (§7, relay
  attribution).
- `notConfirmedByAuthor`, the foreign marker: the author has a live record concurrent with it
  (neither reaches the other) and no live record from the author reaches it, or a live record
  from the author lists it in `disown`.

The foreign marker is decided by reachability and `disown`, never by receive order, because the
server controls receive order. (If it used "A's latest message" by arrival, the server could delay
A's genuine a4 until after Dave imports a dump holding A's a5, and the genuine a5 would be
marked.) **[amendment]**

A fake attributed to member A is exposed when A writes, as follows: **[amendment]**

- **If only the dump holds it** (the dump-giver sends no live message that links it): A's new
  message does not reach it, because A never held it, and is concurrent with it. It is marked
  "not confirmed by A".
- **If a member M also links it live**, it is "held by M". A's client receives M's message,
  fetches the fake and accepts it. A client never refuses a record in its own name, because that
  would stall every record that links it. It alarms locally and adds the fake to A's disown set;
  **every** later message from A carries the full set in `disown`, so any member who receives any
  later message from A live marks the fake "not confirmed by A". Without `disown`, A's next
  message would reach the fake through M's, and a third member could not tell "A wrote it" from
  "M forged it" (`relay_attribution_indistinguishable`). **[amendment]**
- **Limit of the second case.** A member who imports a dump sees the fake as "held by M" until A
  writes again live; A's next live message carries the disown list and settles it. If A never
  writes again, the fake stays "held by M", never "confirmed by A" (§7). **[amendment]**

**The server's role.** It carries the live messages and cannot forge their links, so it cannot
vouch for a bad dump. It can withhold or delay live traffic, which leaves records unconfirmed.
That is visible, but it is not proof against the server: a quiet group, or an offline author,
looks the same. **[amendment]**

## 3. Mechanism

- **Export** (A9): a dump file (`<group>.zrdt`) holds the store blob (`ENCODE`; structure only,
  A4) and a content section keyed by digest. Each content entry is a record's opening (the nonce
  and the committed DataMessage bytes, with fields 15 and 200 already removed, from Desktop's
  `zrdtOpening`). **[amendment]**
  - Content is left out for disappearing (`expireTimer > 0`), deleted-for-everyone and view-once
    messages.
  - The content section never carries the group master key: openings never contain field 15
    (`groupV2`), because the opening is exactly the committed bytes (update §4.5). The importer
    takes the group context from the conversation it imports into.
  - A member who joined after a record was sent gets a **structure-only** dump. It resolves their
    links without giving them pre-join content, and replaces "newcomer pending forever".
    Membership changes after zrdt genesis are otherwise a non-goal (A7).
  - Export requires OS authentication and shows a "do not share" warning, as Signal's own "Export
    chat history" does.
  - Transport is the user's choice of file transfer (AirDrop, USB, a Signal attachment). There is
    no mirror or server transport unless the dump is encrypted.
  - To compare the file with the giver before importing, the giver can send a compare code: copy
    and paste, carrying the full sorted heads set (A11). No QR.
- **Import**: on a device with no store, `OPEN` the blob; on a device with a store, `MERGE` it
  (as `OPEN`, then union; `CheckedStore.abs_merge` says the result holds exactly the records of
  both). On `UNVERIFIABLE`: refuse, show the digests from `missing[]` and `unverifiable[]`, and
  offer "Keep what verifies" (`SALVAGE`: it loads the largest part that verifies, as a
  `CheckedStore`, and lists the dropped digests). On a device that already has a store, `SALVAGE`
  runs under a scratch chat key, and its result is `ENCODE`d and `MERGE`d into the open store, so
  the store only grows. Records the store already held keep their provenance; only new records
  start `imported`. On `COLLISION` or `WRONG_CHAT`: refuse; the open store is unchanged. Then the
  content section: the importer keeps an entry only if its record is in the store and
  `COMMIT(opening) == record.commit`, and refuses entries for disappearing, deleted or view-once
  messages. **[amendment]**
- **Provenance** (A8): the host marks each record with one of three values: **[amendment]**
  - `live`: received through Signal with the envelope sender equal to the record's author, or
    sent by this device;
  - `relayed(by X)`: received by resend from member X, who is not its author;
  - `imported`: from a dump, including records kept by "Keep what verifies".

  Only `live` records count as an author's own, and only `live` records' links are used as
  confirmation sources. A later `live` copy of the same digest upgrades its provenance. The flag
  is host state (`zrdt_provenance`, A7), not part of the record, and the host is trusted to set it
  correctly (listed in the trusted base).
- **Status**: the host passes its live facts to `CLASSIFY` (A3), which returns a status per
  record (§2, stage 2); `classify_spec` proves it computes the spec's status. The host calls it
  after an import and after each live record, and redraws what changed. "Held by" is monotone:
  once a live record reaches a record, it still does as the store grows (`Reach.lift`). Author
  confirmation can be withdrawn by a later `disown`. **[amendment]**
- **Resend by digest** (`ZrdtResendRequest` / `ZrdtResend` / `ZrdtNotFound`, `APP.md` §5) stays
  for small gaps. The request goes 1:1 to the referencing sender first, then to the group; replies
  are 1:1. A relayed record is checked by `zrdtd` (`ACCEPT_RECORD`, protocol 2: the bytes are a
  record, and the opening's commitment is the record's commit, else `BAD_OPENING`) **[amendment]**,
  stored as `relayed(by X)`, and shown "relayed by X" until
  it is author-confirmed. It never applies side-effect fields such as the sender's `profileKey`
  (`handleDataMessage.preload.ts:687-711`). The author fast path (the author re-sends the original
  through Desktop's sendLog, `handleRetry.preload.ts:236-245`) arrives `live`. `ZrdtNotFound` is
  not decisive (A8). The beat-4 rebuild of a rejected store uses "Keep what verifies", not resend.
  **[amendment]**

## 4. Library and refinement additions

The library is `zrdtd` (A3), a Lean process the app talks to in frames. This plan uses these of
its ops: **[amendment]**

| Op | Used for |
|---|---|
| `OPEN` | load a dump on a device with no store |
| `SALVAGE` | "Keep what verifies" |
| `MERGE` | import into an existing store |
| `ENCODE` | export the store blob |
| `COMMIT` | check each content entry, and each relayed opening, against its record |
| `HASH` | check a relayed record against its digest |
| `REACH_SET` | the records one message's links reach (what `CheckedStore.confirmed` is about) |
| `CLASSIFY` | a status per record, from the live facts |

The statements behind them (A5) are `CheckedStore.open_iff`, `CheckedStore.salvage_spec`,
`CheckedStore.abs_merge`, `CheckedStore.encode_open`, `CheckedStore.confirmed` ("held by the
sender") and `CheckedStore.classify_spec`, in `Crdt/Merkle/Api.lean`. Under them are the spec
obligations `confirmed_exact`, `reach_implies_held`, `salvage_maximal` and `authorConfirmed_sound`
in `Chat.lean`, and the limit examples `withheld_tail_undetectable`, `tail_replaced_passes_open`
and `relay_attribution_indistinguishable`. New for this plan, compared with the 2026-10-31 text:
`CLASSIFY` with `classify_spec` (code in `core/Zrdt/Provenance.lean`), `authorConfirmed_sound`,
and the fourth limit example. The dump's content section is host-side and needs only `COMMIT`.
**[amendment]**

## 5. UI

- **Import / Export history** in the conversation menu; for the demo, in Settings → Internal
  (A11). Export asks for OS authentication and shows "do not share". **[amendment]**
- **Unconfirmed section** (A9): after an import, `unconfirmed` records are shown in a collapsed
  section, without avatars or live links, never inline under a member's name. Its header reads
  "N messages not yet confirmed by any member" and counts down as live messages arrive. A record
  leaves the section once a live message reaches it. **[amendment]**
- **Labels** (A8), from `CLASSIFY` and the provenance flag: **[amendment]**
  - grey: nobody has confirmed holding it (`unconfirmed`);
  - "held by X" (`heldBy(X)`);
  - "relayed by X" (provenance `relayed(by X)`, until author-confirmed);
  - normal, "confirmed": confirmed by its author (`confirmedByAuthor`); a `live` record is this by
    construction;
  - "not confirmed by A" (`notConfirmedByAuthor`), the foreign marker. It is decided by
    reachability and `disown`, never by arrival order, so it appears only after A has written live.
- **Own-name alarm** (A8): when this device accepts a record in its user's name that it did not
  create: "someone linked a message in your name you did not send". The record goes into `disown`
  in the next message. **[amendment]**
- The compare screen, gap row and rejected banner are as in `APP.md` §7. Checkpoints and the
  fork marker are optional UI and not part of the demo (`PLAN_HUMANS.md` §6, A8). **[amendment]**

## 6. Demo beat 5, restore from anyone (doctored variant only, 60 s)

**[amendment]** Pre-state: Alice, Bob, Carol and Dave are members of "Camping" from its creation
(the group is static, A7), and Dave's mock phone has received beats 1–4. Dave's desktop is linked
just before this beat, so it has an empty store. `doctor.ts` is hooked into Bob's export: it
automatically appends two fabricated messages attributed to Bob **on top of** Bob's genuine head.
It stands for anyone who tampered with the file on the way. It must run on the live export,
because the digests depend on the live run; the file cannot be prepared in advance (A11).

1. Bob exports `Camping.zrdt` (Settings → Internal), and it goes to Dave by plain file copy (one
   machine; not through the chat). Dave imports it. `OPEN` passes, because appending is not
   caught (§2, stage 0). Screen: the whole history, the two fakes included, in the collapsed
   section and grey, "N messages not yet confirmed by any member". **[amendment]**
2. Alice sends one message. Screen: the genuine history leaves the section and reads "held by
   Alice"; Alice's own messages read "confirmed". The two fakes stay collapsed and grey, because
   Alice never held them. **[amendment]**
3. Bob sends one message. Screen: Bob's genuine messages read "confirmed"; the two fakes are
   marked "not confirmed by Bob" (his message is concurrent with them and does not reach them).
   Carol's messages stay "held by" until Carol writes. **[amendment]**

Each step is one click or one message. Close: "the dump came from a file, from anyone; one
message from Alice told Dave exactly which part of it Alice holds, and one message from Bob
exposed the two messages forged in his name." **[amendment]**

## 7. Limits and trusted items

- Message content and attachment pointers only. Media files are not in the store or the dump;
  they would need their own fetch, and Signal's CDN expires attachments. **[amendment]**
- The provenance flag (`live`, `relayed(by X)`, `imported`) is set by the host. If the host marks
  an imported or relayed record as live, confirmation is meaningless for it. This is a
  trusted-host item alongside "passes the right bytes" and the scope predicate. **[amendment]**
- Attribution uses `live` records only. Imported and relayed records attributed to A never count
  as A's own, and nothing uses "A's latest message" by arrival: the server controls arrival
  order. **[amendment]**
- **Relay attribution.** Without `disown`, "A wrote F and the server dropped it" and "M forged
  F" look the same to a third member (`relay_attribution_indistinguishable`). So a fake that a
  member links live is caught only when A's client disowns it. That needs A's client to be
  honest, to receive M's message, and to write again. Until then the fake is "held by M". The
  disown list is repeated in full in every later message from A (A8), so any member who receives
  any later message from A live sees it, including a member who imported a dump after the first
  disown. If A never writes again, the fake stays "held by M". **[amendment]**
- **Restoring your own device.** A device that imports a dump cannot tell which imported records
  in its own user's name that user wrote: none were created on this device, and none arrived
  live. Disowning them would accuse its own user. Not disowning them lets a dump-giver append
  fakes in the user's name on top of the head: the device's next message links them, and every
  member then shows them as confirmed by that user. Until this is designed, attribution in this
  plan covers records in other members' names, as in beat 5, where the fakes are in Bob's name.
  The same limit applies to an account with more than one zrdt device. **[amendment]**
- A dump-giver colluding with the server can keep a device partitioned (no live traffic), so
  nothing is ever confirmed. Visible, not preventable, and not proof against the server: a quiet
  group looks the same. **[amendment]**
- **Privacy** (A9). A dump leaves Signal's encryption. It omits the content of disappearing,
  deleted and view-once messages, but the structure of expired messages (authors, causal shape,
  count) persists in every store and every dump. Links are receipts visible to the whole group
  (A12). Export is gated by OS authentication and a warning; what the user does with the file
  after that is outside zrdt. **[amendment]**
- **Stock restore** (A9). Stock link-and-sync and Signal backups carry no zrdt data. A device
  restored that way has a full timeline and an empty store; how its rows are matched to records
  is out of scope. **[amendment]**
- Membership changes after zrdt genesis are a non-goal (A7). A member who joined later gets a
  structure-only dump, which resolves links but gives no pre-join content. **[amendment]**
- Every theorem below ends in "or two records collide", as everywhere in `Crdt/Merkle`.
- Phase 2 (signatures inside records) would make dump records self-authenticating on import, and
  would remove the wait for the author to write again. It is not in this plan: attribution here
  comes from the author's own live messages and `disown`. Signatures have a cost: a signed record
  proves to anyone who holds a copy, a dump included, that its author wrote it. That gives up the
  deniability Signal's messages have. **[amendment]**

## 8. Amendments to the other documents

The review amendments are in `docs/review-2026-11-01/AMENDMENTS.md`. They were applied on
2026-11-01 to `PLAN.md`, `APP.md`, `PLAN_HUMANS.md` and this file, on top of the 2026-10-31
`CheckedStore` rewrite. **[amendment]**

## Appendix: the theorems, as proved in scratch

These compile against `Crdt/Merkle/Integrity.lean` as of 2026-10-31 and depend only on
`[propext, Classical.choice, Quot.sound]`. They remain valid spec lemmas after the review.
`reachSet` is a spec-level definition and is `noncomputable`; the executable version is
`CheckedStore.reachSet` in `core/Zrdt/Store.lean`, and `CheckedStore.confirmed` (A5) states
`confirmed_exact` over it. **[amendment]**

```lean
import Crdt.Merkle.Integrity
open Crdt.Merkle
variable {α H K : Type*} [DecidableEq α] [DecidableEq H] [DecidableEq K]
variable (hash : Record α H K → H)

open Classical in
/-- The records of `s` that can be reached from the hashes `hs`. -/
noncomputable def reachSet (s : Store α H K) (hs : Finset H) : Store α H K :=
  s.filter fun r ↦ Reach hash s hs (hash r)

theorem mem_reachSet {s : Store α H K} {hs : Finset H} {r : Record α H K} :
    r ∈ reachSet hash s hs ↔ r ∈ s ∧ Reach hash s hs (hash r) := by
  simp [reachSet, Finset.mem_filter]

/-- A reach path only passes through reachable records, so it survives restriction. -/
theorem reach_reachSet {s : Store α H K} {hs : Finset H} {d : H} (h : Reach hash s hs d) :
    Reach hash (reachSet hash s hs) hs d := by
  induction h with
  | head hd => exact .head hd
  | @link r d hr hreach hl ih => exact .link ((mem_reachSet hash).mpr ⟨hr, hreach⟩) ih hl

/-- In a closed store, the records reachable from resolving hashes are a fetched store. -/
theorem fetched_reachSet {s : Store α H K} {hs : Finset H} (hc : Closed hash s)
    (hh : hs ⊆ digests hash s) : Fetched hash (reachSet hash s hs) hs := by
  refine ⟨fun d hd ↦ ?_, fun r hr ↦ reach_reachSet hash ((mem_reachSet hash).mp hr).2⟩
  have hd' : Reach hash s hs d :=
    hd.lift hash (fun r hr ↦ ((mem_reachSet hash).mp hr).1) (fun d hd ↦ .head hd)
  obtain ⟨r, hr, he⟩ := complete_of_closed hash hc hh d hd'
  exact ⟨r, (mem_reachSet hash).mpr ⟨hr, he ▸ hd'⟩, he⟩

/-- **Confirmation is exact.** Whatever a member's message points at in your store is, record
for record, what that member holds behind those links. Or two records collide. -/
theorem confirmed_exact {s t : Store α H K} {hs : Finset H} (hcs : Closed hash s)
    (hct : Closed hash t) (hhs : hs ⊆ digests hash s) (hht : hs ⊆ digests hash t) :
    reachSet hash s hs = reachSet hash t hs ∨
      CollisionIn hash (reachSet hash s hs ∪ reachSet hash t hs) :=
  fetched_agree hash (fetched_reachSet hash hcs hhs) (fetched_reachSet hash hct hht)

/-- A member's message reaches a record only if the member holds it. Or a collision. -/
theorem reach_implies_held {t : Store α H K} {hs : Finset H} {f : Record α H K}
    (hct : Closed hash t) (hh : hs ⊆ digests hash t) (hreach : Reach hash t hs (hash f)) :
    f ∈ t ∨ CollisionIn hash (insert f t) := by
  obtain ⟨r, hr, he⟩ := complete_of_closed hash hct hh _ hreach
  by_cases hrf : r = f
  · exact Or.inl (hrf ▸ hr)
  · exact Or.inr (CollisionIn.of_mem hash (Finset.mem_insert_of_mem hr)
      (Finset.mem_insert_self f t) hrf he)

```

`reach_implies_held` is kept as a spec lemma, not advertised. A third statement from the scratch
file, `latest_reaches_all_own` (an honest member's latest message reaches every record that member
holds), is not added and backs nothing: "latest" depends on arrival order, which the server
controls. The foreign marker is `CLASSIFY`'s `notConfirmedByAuthor`, backed by `classify_spec` and
`authorConfirmed_sound`. **[amendment]**

**Status (2026-11-01):** all of the following are now proved in `Chat.lean`, and the code-level
statements in `Api.lean` are proved and gated (`PLAN.md` §3.2, §10). **[amendment]**

**To prove or add** (phase A, `Chat.lean`; done): **[amendment]**

- `authorConfirmed_sound`. The definition: `authorConfirmed r` holds when some `live` record from
  `r.author` reaches r, and no `live` record from `r.author` lists r in `disown`. The statement in
  words: if an author's client is honest, meaning it disowns every accepted record in its own name
  that it did not create, then every author-confirmed record attributed to that author was created
  by it, or two records collide.
- `relay_attribution_indistinguishable` (limit example, `decide` over a toy hash). In world 1,
  Alice wrote F, the server dropped it to Carol, and Mallory's live message links it. In world 2,
  Mallory forged F and her live message links it. Without `disown`, Carol's view is the same in
  both.
- `tail_replaced_passes_open` (limit example): two concrete stores share a prefix, differ after
  it, and both pass `open`. It is the rewritten-tail counterpart of `withheld_tail_undetectable`.

How the stages map to the statements: **[amendment]**

- Stage 0 is `CheckedStore.open_iff`, `CheckedStore.salvage_spec` and `salvage_maximal` (phase
  B). Its limits are `withheld_tail_undetectable` and `tail_replaced_passes_open`.
- Stage 1 is `confirmed_exact` (over the code, `CheckedStore.confirmed`), with `s` the importing
  device's store, `t` the sender's store and `hs` the sender's message's links. `hht` holds for an
  honest sender, which accepted its own message; `hhs` is the "links resolve" case. It says "held
  by the sender", nothing about authors.
- Stage 2 is `reach_implies_held` (a fake is not in `t`, so not reached), `authorConfirmed_sound`
  (who wrote what) and `classify_spec` (the UI's statuses are the spec's). Its limit is
  `relay_attribution_indistinguishable`.
