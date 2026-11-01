# RESTORE_PLAN: restore a chat from anyone, verify it with the next live message

Status: follow-up to `PLAN.md`, `PLAN_HUMANS.md` and `APP.md`, written 2026-10-31. The theorems
in the appendix are proved in a scratch file against the current build (standard axioms only) and
are to be added to `Crdt/Merkle/Chat.lean` in phase A. Nothing here is in the repository yet.

## 1. What this adds

Today's plan recovers a few missing messages by asking the group for them by digest. This
document specs the general case: a device with no history (new device, wiped device, new member
who should get history, a device whose stored copy failed `check`) gets the **whole history as a
dump from anyone, by any means**, and verifies it without trusting the source.

The source can be a member sending a file over AirDrop, USB or a Signal attachment, a backup, a
mirror, or the server. It does not matter, because:

1. On import, `check` proves the dump is internally consistent.
2. The first live message from any member confirms, exactly, everything that message points at.
3. Anything no member's message ever points at stays marked unconfirmed, and a fake attributed
   to an active member is exposed the next time that member writes.

Signal has no peer history sync: it moves history from a primary phone to its own linked devices,
and it has encrypted backups to its own servers, both same-account; new group members get no
history. Peer sync is unsafe without something like this, because a peer could hand you a doctored
history. With it, any peer will do.

## 2. What "correct" means, at each stage

**Stage 0, on import.** `zrdt_decode` recomputes every digest; `zrdt_check` passes iff every link
resolves (`Complete`) and every record is reachable from the dump's heads (`Tight`). This rules
out a record removed from the middle, any altered record, and corruption, because each of those
breaks a link of everything after it. It cannot rule out a **stale** dump (a prefix) or a dump
whose **whole tail was replaced** by a consistent fake. Both are valid histories that end
somewhere. `withheld_tail_undetectable` is exactly this limit.

**Stage 1, the first live message from a member.** Signal authenticates the sender, so the
message's links are that member's real heads. Two cases:

- The links resolve in your store. Then the records reachable from them in your store are,
  record for record, the records reachable from them in the member's store. Or two records
  collide. (`confirmed_exact`.) One message from a current member confirms the whole history
  except the newest concurrent branches.
- Some link does not resolve. The dump was missing those records; `accept` names the digests
  (`accept_rejects_names_missing`); the app fetches them. Stale, not wrong.

**Stage 2, what stays unconfirmed.** Records no member's message reaches: the newest messages,
which will be confirmed shortly, and fabricated ones, which never will be, because a member's
message reaches a record only if the member holds it (`reach_implies_held`). A fake attributed to
member A is exposed the next time A writes: A's latest message reaches every genuine record of
A's (`latest_reaches_all_own`) and not the fake.

**The server's role.** It carries the live messages and cannot forge their links, so it cannot
vouch for a bad dump. It can only withhold live traffic, which leaves everything unconfirmed,
and that is itself the warning.

## 3. Mechanism

- **Export**: `zrdt_encode(store)` to a file (`<group>.zrdt`), plus the heads as a QR or word
  list if the receiver wants to compare before importing. Transport is the user's choice.
- **Import**: `zrdt_decode` → `zrdt_check` → on `ok`, `zrdt_merge` into the current store
  (`fetched_union` says the merge is a checked store from the union of head sets). On
  `missing(d)` or `unreachable(d)`: refuse, show the digest, offer "import anyway as unconfirmed"
  only if a product decision wants it (not in the demo).
- **Provenance**: the host marks each record `live` (received through Signal from an
  authenticated sender, or sent by this device) or `imported`. Only `live` records' links are
  used as confirmation sources. This flag is host state, not part of the record, and the host is
  trusted to set it correctly (listed in the trusted base).
- **Confirmed set**: the records reachable, within the store, from the links of all `live`
  records. Recomputed incrementally: when a live record arrives, add the reach set of its links
  (one traversal from a few hashes, stopping at already-confirmed records). Monotone: once
  confirmed, always confirmed (`Reach.lift`).
- **Resend by digest** (`ZrdtResendRequest`/`ZrdtResend`, `APP.md` §5) stays for small gaps.
  The beat-4 rebuild of a rejected store uses import, not resend.

## 4. Library and refinement additions

C API (`PLAN.md` §3.3) gets one function, batched so the host does not loop:

```c
zrdt_digests zrdt_reach_set(const zrdt_store *, const zrdt_digest *from, size_t nfrom);
/* digests of every record reachable from `from`, following links within the store */
```

`Impl.lean`: `reachSet : ChatStore → List Digest → List Digest` (worklist, `termination_by`).
`Refine.lean`: `reachSet_iff : Inv c → (d ∈ c.reachSet hs ↔ ∃ r ∈ abs c, hash r = d ∧ Reach hashRecord (abs c) hs.toFinset d)`.
Spec side: the definitions in the appendix.

## 5. UI

- **Import / Export history** in the conversation menu (dev menu is fine for the demo).
- **Confirmed badge** per message: `live` records are confirmed by construction; `imported`
  records show grey until confirmed, then normal. The transition is the demo.
- **Unconfirmed banner** after an import: "N messages not yet confirmed by any member". It
  counts down as live messages arrive.
- **Foreign marker**: an imported record attributed to A that A's latest live message does not
  reach, while A's genuine records are reached: "not confirmed by A". Shown only after A has
  written at least once since the import.
- The compare screen, gap placeholder, rejected banner, checkpoint and fork marker are as in
  `APP.md` §7.

## 6. Demo beat 5 (replaces the "re-fetch from a member" step of beat 4)

Pre-state: Alice, Bob, Carol have chatted (beats 1–3). Dave is a fourth member with a fresh
desktop and an empty store.

1. Bob exports `Camping.zrdt` and sends it to Dave by file (AirDrop or a plain file copy; not
   through the chat). Dave imports it. Screen: the whole history appears, every message grey,
   banner "27 messages not yet confirmed by any member".
2. Alice sends one message. Screen: everything up to Alice's heads turns normal at once, the
   banner reads "0 messages not yet confirmed", Alice's new message is live.
3. Doctored variant: Dave resets, imports `Camping-doctored.zrdt` (made by `demo/doctor.ts`:
   the tail replaced by two fabricated messages attributed to Bob). `check` passes; everything
   is grey. Alice sends one message. Screen: the genuine history turns normal; the two fabricated
   messages stay grey. Bob sends one message. Screen: the two fabricated messages get the
   foreign marker "not confirmed by Bob".

Each step is one click or one message; the whole beat is under a minute. Close: "the dump came
from a file, from anyone; one message from a real member told Dave exactly which part of it was
real."

## 7. Limits and trusted items

- Text, timestamps and attachment digests only. Media is not in the store; it would need its own
  fetch, and Signal's CDN expires attachments.
- The `live`/`imported` flag is set by the host. If the host marks an imported record as live,
  confirmation is meaningless for it. This is a trusted-host item alongside "passes the right
  bytes".
- "A's latest message" means the most recent record from A received through Signal. Imported
  records attributed to A are never used to identify A's latest.
- A dump-giver colluding with the server can keep a device partitioned (no live traffic), so
  nothing is ever confirmed. Visible, not preventable.
- Every theorem below ends in "or two records collide", as everywhere in `Crdt/Merkle`.
- Phase 2 (signatures inside records) would make dump records self-authenticating on import.
  Not needed for this plan; confirmation by live links does the job without it.

## 8. Amendments to the other documents (to apply when this plan is accepted)

- `PLAN.md` §3.3: add `zrdt_reach_set`. §4 phase A: add the appendix theorems and the
  rewritten-tail countermodel to `Chat.lean`; gate `confirmed_exact`. §4 phase B: `reachSet`
  in `Impl.lean`, `reachSet_iff` in `Refine.lean`. §4 phase D: import/export, provenance flag,
  confirmed set, badges. §8: beat 5. §7: the trusted-host flag.
- `APP.md` §5–§7: import path replaces "re-fetch from a member"; provenance flag on the message
  model (`zrdtProvenance: 'live' | 'imported'`); confirmed set in the conversation state;
  `demo/doctor.ts` gains the "replace tail with fakes" mode. §9: beat 5.
- `PLAN_HUMANS.md` §4: theorem (7) `confirmed_exact` with the two supporting statements; §6:
  the confirmed badge; §8: import from anyone.

## Appendix: the theorems, as proved in scratch

These compile against `Crdt/Merkle/Integrity.lean` as of today and depend only on
`[propext, Classical.choice, Quot.sound]`. `reachSet` is a spec-level definition and is
`noncomputable`; the executable version is `ChatStore.reachSet` in `Impl.lean`.

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

/-- An honest member's latest message reaches every record that member holds. -/
theorem latest_reaches_all_own {t : Store α H K} {hs : Finset H} (hf : Fetched hash t hs)
    {m : Record α H K} (hm : m.links = hs) : ∀ r ∈ t, Reach hash t m.links (hash r) := by
  rw [hm]; exact hf.2
```

How the stages map to the statements: stage 0 is `check_iff_fetched` (phase B); stage 1 is
`confirmed_exact` with `s` the importing device's store, `t` the member's store and `hs` the
member's message's links (`hht` holds because the member accepted its own message; `hhs` is the
"links resolve" case); stage 2 is `reach_implies_held` (a fake is not in `t`, so not reached) and
`latest_reaches_all_own` (A's genuine records are reached). To add alongside: an `example` with
two concrete stores that share a prefix, differ after it, and both pass `check`, as the
rewritten-tail counterpart of `withheld_tail_undetectable`.
