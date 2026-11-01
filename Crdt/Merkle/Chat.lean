/-
Copyright (c) 2026 zrdt contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: zrdt contributors
-/
import Mathlib
import Crdt.Merkle.Defs
import Crdt.Merkle.Integrity

set_option linter.unusedSectionVars false

/-!
# Hash-linked records: what the chat relies on

The statements about the shipped code (`Api.lean`) are proved from the theorems in this file.
They are proof obligations, not results on their own (`docs/PLAN.md` §3.2).

* **Merging.** `fetched_union`: the union of two fetched stores is fetched from the union of
  their start hashes. `heads_union_subset`: the heads of a union are heads of one side.
* **A live message confirms what its sender holds.** `reachSet` is the part of a store a
  message's links reach. `confirmed_exact`: that part is, record for record, the same in your
  store and in the sender's. `reach_implies_held`: a message reaches a record only if its sender
  holds it.
* **Accept-built stores and salvage.** `AcceptBuilt`: some order accepted every record.
  `buildRetry` is "keep what verifies". `salvage_built` and `salvage_maximal`: it keeps an
  accept-built store, and the largest one. `acceptBuilt_union`, `acceptBuilt_insert`: merging and
  accepting keep a store accept-built. `fetched_build`: an accept-built store is fetched from its
  own heads.
* **Who wrote a record.** `LiveFacts` is what the host knows about how records arrived.
  `authorConfirmed` and `status` give the label the app shows. `authorConfirmed_sound`: if the
  author's app disowns what it did not write, an author-confirmed record was written by its
  author.
* **Four limits.** `withheld_tail_undetectable`, `tail_replaced_passes_open`,
  `gap_indistinguishable`, `relay_attribution_indistinguishable`: what links alone cannot do.

Every conclusion that compares two stores ends in `∨ CollisionIn hash u`, as in `Integrity.lean`.
Every definition here is computable, so the examples are checked by `decide`.
-/

namespace Crdt.Merkle

/-! ## Toy records for the examples -/

namespace Toy

/-- A record written after seeing `r1`. Hash `2`. -/
def r2 : R := ⟨2, {1}, ()⟩

/-- A record written after seeing `r0`, at the same time as `r1` (neither saw the other).
Hash `3`. -/
def r3 : R := ⟨3, {0}, ()⟩

/-- A record written after seeing `r2`. Hash `4`. -/
def r4 : R := ⟨4, {2}, ()⟩

/-- A fake that replaces `r2`: it links `r1` like `r2` does. Hash `12`. -/
def f2 : R := ⟨12, {1}, ()⟩

/-- A fake that replaces `r4`: it links `f2`. Hash `14`. -/
def f4 : R := ⟨14, {12}, ()⟩

/-- The record `fake0` links. Hash `7`. -/
def r7 : R := ⟨7, ∅, ()⟩

/-- Half of a cycle: links hash `6`. Hash `5`. -/
def c5 : R := ⟨5, {6}, ()⟩

/-- The other half of the cycle: links hash `5`. Hash `6`. -/
def c6 : R := ⟨6, {5}, ()⟩

end Toy

/-! The "Camping" chat, used for the examples about authors. Members are numbers. -/

namespace Camping

/-- Records of the Camping chat: numbers as payloads and as hashes, numbers as authors. -/
abbrev R := Record ℕ ℕ ℕ

/-- Toy hash: a record's hash is its payload. -/
def hash (r : R) : ℕ := r.payload

/-- Alice. -/
def alice : ℕ := 0

/-- Bob. -/
def bob : ℕ := 1

/-- Mallory, a member who makes things up. -/
def mallory : ℕ := 3

/-- Alice: "who's bringing the tent?". Hash `0`. -/
def tent : R := ⟨0, ∅, alice⟩

/-- Bob: "me". Hash `1`. -/
def me : R := ⟨1, {0}, bob⟩

/-- A fake in Bob's name, added on top of `me` in a doctored dump. Hash `7`. -/
def fake1 : R := ⟨7, {1}, bob⟩

/-- A second fake in Bob's name, on top of `fake1`. Hash `8`. -/
def fake2 : R := ⟨8, {7}, bob⟩

/-- Alice's live message after Dave imported the dump. It links `me`. Hash `5`. -/
def a5 : R := ⟨5, {1}, alice⟩

/-- Bob's live message after `a5`. It links `a5`. Hash `6`. -/
def b6 : R := ⟨6, {5}, bob⟩

/-- Mallory's live message that links the fake `fake2`. Hash `9`. -/
def relink : R := ⟨9, {8}, mallory⟩

/-- Bob's live message after `relink`. It links `relink`, so it reaches the fakes. Hash `10`. -/
def b10 : R := ⟨10, {9}, bob⟩

/-- Demo beat 5. Dave imported Bob's dump, onto which the two fakes were added, and then
received Alice's live `a5`. -/
def daveA : Store ℕ ℕ ℕ := {tent, me, fake1, fake2, a5}

/-- Dave's store after Bob's live `b6` arrives too. -/
def daveB : Store ℕ ℕ ℕ := {tent, me, fake1, fake2, a5, b6}

/-- Bob's own store in beat 5. The fakes were added to his dump on the way, so he never held
them. -/
def bobStore : Store ℕ ℕ ℕ := {tent, me, a5, b6}

/-- A store where Mallory linked `fake2` live (`relink`), and Bob's `b10` came after. -/
def relinked : Store ℕ ℕ ℕ := {tent, me, fake1, fake2, relink, b10}

end Camping

section Spec

variable {α H K : Type*} [DecidableEq α] [DecidableEq H] [DecidableEq K]
variable (hash : Record α H K → H)
variable {s t u : Store α H K} {hs : Finset H}

/-! ## Deciding reachability

`Reach` is defined by its rules (`Defs.lean`). To check it on examples, and to make `reachSet`
computable, we compute the reachable hashes by rounds and prove that this gives exactly `Reach`.
-/

/-- One round of following links: the hashes in `R`, plus the links of every record of `s`
whose hash is in `R`. -/
def reachStep (s : Store α H K) (R : Finset H) : Finset H :=
  R ∪ (s.filter fun r ↦ hash r ∈ R).biUnion Record.links

example : reachStep Toy.hash {Toy.r0, Toy.r1} {1} = {0, 1} := by decide

/-- The hashes reached from `hs` in at most `n` rounds. -/
def reachRounds (s : Store α H K) (hs : Finset H) : ℕ → Finset H
  | 0 => hs
  | n + 1 => reachStep hash s (reachRounds s hs n)

example : reachRounds Toy.hash {Toy.r0, Toy.r1, Toy.r2} {2} 1 = {1, 2} := by decide

/-- All hashes reachable from `hs`. The number of rounds is the number of hashes that could
ever be reached (start hashes and links), which is enough (`mem_reachable`). -/
def reachable (s : Store α H K) (hs : Finset H) : Finset H :=
  reachRounds hash s hs (hs ∪ s.biUnion Record.links).card

example : reachable Toy.hash {Toy.r0, Toy.r1, Toy.r2} {2} = {0, 1, 2} := by decide

/-- A round only adds hashes. -/
theorem reachRounds_succ_subset (n : ℕ) :
    reachRounds hash s hs n ⊆ reachRounds hash s hs (n + 1) :=
  Finset.subset_union_left

/-- Later rounds hold more hashes. -/
theorem reachRounds_mono : Monotone (reachRounds hash s hs) :=
  monotone_nat_of_le_succ fun n ↦ reachRounds_succ_subset hash n

/-- Every hash found in some round is reachable. -/
theorem reach_of_mem_reachRounds {n : ℕ} {d : H} (h : d ∈ reachRounds hash s hs n) :
    Reach hash s hs d := by
  induction n generalizing d with
  | zero => exact .head h
  | succ n ih =>
    rcases Finset.mem_union.mp h with h | h
    · exact ih h
    · obtain ⟨r, hr, hd⟩ := Finset.mem_biUnion.mp h
      obtain ⟨hrs, hrR⟩ := Finset.mem_filter.mp hr
      exact .link hrs (ih hrR) hd

/-- Rounds only find start hashes and links. -/
theorem reachRounds_subset_bound (n : ℕ) :
    reachRounds hash s hs n ⊆ hs ∪ s.biUnion Record.links := by
  induction n with
  | zero => exact Finset.subset_union_left
  | succ n ih =>
    refine Finset.union_subset ih ?_
    exact (Finset.biUnion_subset_biUnion_of_subset_left _ (Finset.filter_subset _ _)).trans
      Finset.subset_union_right

/-- After round `n + 1`, either the round changed nothing, or at least `n + 1` hashes have been
found. -/
theorem reachRounds_stable_or_large (n : ℕ) :
    reachRounds hash s hs (n + 1) = reachRounds hash s hs n ∨
      n + 1 ≤ (reachRounds hash s hs (n + 1)).card := by
  induction n with
  | zero =>
    by_cases h : reachRounds hash s hs 1 = reachRounds hash s hs 0
    · exact Or.inl h
    · right
      have := Finset.card_lt_card
        (Finset.ssubset_iff_subset_ne.mpr ⟨reachRounds_succ_subset hash 0, Ne.symm h⟩)
      omega
  | succ n ih =>
    by_cases h : reachRounds hash s hs (n + 2) = reachRounds hash s hs (n + 1)
    · exact Or.inl h
    · right
      have hne : reachRounds hash s hs (n + 1) ≠ reachRounds hash s hs n := by
        intro he
        apply h
        calc reachRounds hash s hs (n + 2)
            = reachStep hash s (reachRounds hash s hs (n + 1)) := rfl
          _ = reachStep hash s (reachRounds hash s hs n) := by rw [he]
          _ = reachRounds hash s hs (n + 1) := rfl
      have h1 := ih.resolve_left hne
      have := Finset.card_lt_card
        (Finset.ssubset_iff_subset_ne.mpr ⟨reachRounds_succ_subset hash (n + 1), Ne.symm h⟩)
      omega

/-- `reachable` is exactly `Reach`. -/
theorem mem_reachable {d : H} : d ∈ reachable hash s hs ↔ Reach hash s hs d := by
  constructor
  · intro h
    exact reach_of_mem_reachRounds hash h
  · intro h
    set N := (hs ∪ s.biUnion Record.links).card
    have hfix : reachRounds hash s hs (N + 1) = reachRounds hash s hs N := by
      rcases reachRounds_stable_or_large hash N with h' | h'
      · exact h'
      · have := Finset.card_le_card (reachRounds_subset_bound hash (s := s) (hs := hs) (N + 1))
        omega
    have h0 : hs ⊆ reachRounds hash s hs N := fun d hd ↦
      reachRounds_mono hash (Nat.zero_le N) hd
    refine Reach.mem_of_bound hash h0 (fun r hr hrR d hd ↦ ?_) h
    rw [← hfix]
    exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨r, Finset.mem_filter.mpr ⟨hr, hrR⟩, hd⟩)

instance (s : Store α H K) (hs : Finset H) (d : H) : Decidable (Reach hash s hs d) :=
  decidable_of_iff _ (mem_reachable hash)

example : Reach Toy.hash {Toy.r0, Toy.r1} {1} 0 := by decide
-- Links point back in time: from `r0` you do not reach `r1`.
example : ¬ Reach Toy.hash {Toy.r0, Toy.r1} {0} 1 := by decide

/-- `Complete` checked on the finite set of reachable hashes. -/
theorem complete_iff : Complete hash s hs ↔ reachable hash s hs ⊆ digests hash s := by
  constructor
  · intro h d hd
    exact (mem_digests hash).mpr (h d ((mem_reachable hash).mp hd))
  · intro h d hd
    exact (mem_digests hash).mp (h ((mem_reachable hash).mpr hd))

instance (s : Store α H K) (hs : Finset H) : Decidable (Complete hash s hs) :=
  decidable_of_iff _ (complete_iff hash).symm

instance (s : Store α H K) (hs : Finset H) : Decidable (Tight hash s hs) := by
  unfold Tight; infer_instance

instance (s : Store α H K) (hs : Finset H) : Decidable (Fetched hash s hs) := by
  unfold Fetched; infer_instance

example : Fetched Toy.hash {Toy.r0, Toy.r1} {1} := by decide
-- Not tight: nothing reachable from `0` reaches `r1`.
example : ¬ Fetched Toy.hash {Toy.r0, Toy.r1} {0} := by decide
-- Not complete: `r1` links `0`, which the store does not hold.
example : ¬ Fetched Toy.hash {Toy.r1} {1} := by decide

/-! ## Instances of the integrity theorems -/

-- Two phones; the second received `r1` before `r0`, then both again. Same heads, same store.
example : build Toy.hash [Toy.r0, Toy.r1] = build Toy.hash [Toy.r1, Toy.r0, Toy.r1, Toy.r0] ∨
    CollisionIn Toy.hash
      (build Toy.hash [Toy.r0, Toy.r1] ∪ build Toy.hash [Toy.r1, Toy.r0, Toy.r1, Toy.r0]) :=
  fetched_agree Toy.hash (hs := {1}) (by decide) (by decide)
-- Why the collision clause is needed: both stores are fetched from `{1}` and differ, because
-- `r0` and `fake0` have the same hash `0`. The theorem then names that collision.
example : Fetched Toy.hash {Toy.r0, Toy.r1} {1} ∧ Fetched Toy.hash {Toy.fake0, Toy.r1, Toy.r7} {1} ∧
    ({Toy.r0, Toy.r1} : Store ℕ ℕ Unit) ≠ {Toy.fake0, Toy.r1, Toy.r7} ∧
    CollisionIn Toy.hash ({Toy.r0, Toy.r1} ∪ {Toy.fake0, Toy.r1, Toy.r7}) := by
  decide

example : Fetched Toy.hash (build Toy.hash [Toy.r0, Toy.r1, Toy.r3])
      (heads Toy.hash (build Toy.hash [Toy.r0, Toy.r1, Toy.r3])) ∨
    CollisionIn Toy.hash (build Toy.hash [Toy.r0, Toy.r1, Toy.r3]) :=
  fetched_of_build Toy.hash _

-- `r0` and `fake0` have the same hash, so they collide.
example : Toy.r0 = Toy.fake0 ∨ CollisionIn Toy.hash {Toy.r0, Toy.fake0} :=
  accept_unique Toy.hash (d := 0) rfl rfl

-- Adding `r1` to `{r0}`: `r1` becomes the head, and `0` stops being one.
example : heads Toy.hash (insert Toy.r1 {Toy.r0}) = insert 1 (heads Toy.hash {Toy.r0} \ {0}) ∨
    CollisionIn Toy.hash (insert Toy.r1 {Toy.r0}) :=
  heads_insert Toy.hash (by decide) (by decide) (by decide)

example : ({Toy.r0, Toy.r1} : Store ℕ ℕ Unit) = {Toy.r1, Toy.r0} ∨
    CollisionIn Toy.hash ({Toy.r0, Toy.r1} ∪ {Toy.r1, Toy.r0}) :=
  eq_of_digests_eq Toy.hash (by decide)

/-! ## Merging -/

/-- In a fetched store every link resolves. -/
theorem closed_of_fetched (h : Fetched hash s hs) : Closed hash s :=
  fun r hr d hd ↦ h.1 d (.link hr (h.2 r hr) hd)

/-- The heads of a merged store are heads of one of the two stores. Some heads can be lost: a
record of one store can link a head of the other. -/
theorem heads_union_subset (s t : Store α H K) :
    heads hash (s ∪ t) ⊆ heads hash s ∪ heads hash t := by
  intro d hd
  obtain ⟨r, hr, rfl, hh⟩ := (mem_heads hash).mp hd
  rcases Finset.mem_union.mp hr with hr' | hr'
  · exact Finset.mem_union_left _ ((mem_heads hash).mpr
      ⟨r, hr', rfl, fun y hy ↦ hh y (Finset.mem_union_left _ hy)⟩)
  · exact Finset.mem_union_right _ ((mem_heads hash).mpr
      ⟨r, hr', rfl, fun y hy ↦ hh y (Finset.mem_union_right _ hy)⟩)

example : heads Toy.hash ({Toy.r0} ∪ {Toy.r0, Toy.r1}) ⊆
    heads Toy.hash {Toy.r0} ∪ heads Toy.hash {Toy.r0, Toy.r1} :=
  heads_union_subset Toy.hash _ _
-- The head `0` of `{r0}` is lost in the union, because `r1` links it.
example : heads Toy.hash ({Toy.r0} ∪ {Toy.r0, Toy.r1}) = {1} := by decide

/-- **Merging two fetched stores.** If `s` is fetched from `hs` and `t` from `ht`, then `s ∪ t`
is fetched from `hs ∪ ht`. No collision clause is needed. -/
theorem fetched_union {ht : Finset H} (hS : Fetched hash s hs) (hT : Fetched hash t ht) :
    Fetched hash (s ∪ t) (hs ∪ ht) := by
  refine ⟨fun d hd ↦ ?_, fun r hr ↦ ?_⟩
  · cases hd with
    | head h =>
      rcases Finset.mem_union.mp h with h | h
      · obtain ⟨x, hx, he⟩ := hS.1 d (.head h)
        exact ⟨x, Finset.mem_union_left _ hx, he⟩
      · obtain ⟨x, hx, he⟩ := hT.1 d (.head h)
        exact ⟨x, Finset.mem_union_right _ hx, he⟩
    | link hr _ hl =>
      rcases Finset.mem_union.mp hr with hr | hr
      · obtain ⟨x, hx, he⟩ := closed_of_fetched hash hS _ hr d hl
        exact ⟨x, Finset.mem_union_left _ hx, he⟩
      · obtain ⟨x, hx, he⟩ := closed_of_fetched hash hT _ hr d hl
        exact ⟨x, Finset.mem_union_right _ hx, he⟩
  · rcases Finset.mem_union.mp hr with hr | hr
    · exact (hS.2 r hr).lift hash Finset.subset_union_left
        (fun d hd ↦ .head (Finset.mem_union_left _ hd))
    · exact (hT.2 r hr).lift hash Finset.subset_union_right
        (fun d hd ↦ .head (Finset.mem_union_right _ hd))

example : Fetched Toy.hash ({Toy.r0, Toy.r1} ∪ {Toy.r0, Toy.r3}) ({1} ∪ {3}) :=
  fetched_union Toy.hash (by decide) (by decide)

/-! ## What a live message confirms -/

/-- The records of `s` reached from the hashes `hs`. For a live message with links `hs`, these
are the records it confirms its sender holds (`confirmed_exact`). -/
def reachSet (s : Store α H K) (hs : Finset H) : Store α H K :=
  s.filter fun r ↦ Reach hash s hs (hash r)

example : reachSet Toy.hash {Toy.r0, Toy.r1, Toy.r3} {1} = {Toy.r0, Toy.r1} := by decide
-- `r3` was written at the same time as `r1`, so a message that links `1` does not reach it.
example : Toy.r3 ∉ reachSet Toy.hash {Toy.r0, Toy.r1, Toy.r3} {1} := by decide
#guard reachSet Toy.hash {Toy.r0, Toy.r1, Toy.r2, Toy.r3} {2} = {Toy.r0, Toy.r1, Toy.r2}

/-- A record is in `reachSet` when it is in the store and reached. -/
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

example : Fetched Toy.hash (reachSet Toy.hash {Toy.r0, Toy.r1, Toy.r3} {1}) {1} :=
  fetched_reachSet Toy.hash (by decide) (by decide)

/-- **Confirmation is exact.** Your store `s` and a member's store `t` are both closed, and a
live message from that member has links `hs` that resolve in both. Then what those links reach
in your store is, record for record, what they reach in the member's store. Or two records
collide. It says the member holds these records; it says nothing about who wrote them. -/
theorem confirmed_exact {s t : Store α H K} {hs : Finset H} (hcs : Closed hash s)
    (hct : Closed hash t) (hhs : hs ⊆ digests hash s) (hht : hs ⊆ digests hash t) :
    reachSet hash s hs = reachSet hash t hs ∨
      CollisionIn hash (reachSet hash s hs ∪ reachSet hash t hs) :=
  fetched_agree hash (fetched_reachSet hash hcs hhs) (fetched_reachSet hash hct hht)

-- Your store holds `r3`, the sender's holds `r2`; a message that links `1` reaches `{r0, r1}`
-- in both.
example : reachSet Toy.hash {Toy.r0, Toy.r1, Toy.r3} {1} =
      reachSet Toy.hash {Toy.r0, Toy.r1, Toy.r2} {1} ∨
    CollisionIn Toy.hash (reachSet Toy.hash {Toy.r0, Toy.r1, Toy.r3} {1} ∪
      reachSet Toy.hash {Toy.r0, Toy.r1, Toy.r2} {1}) :=
  confirmed_exact Toy.hash (by decide) (by decide) (by decide) (by decide)

/-- A member's message reaches a record only if the member holds it. Or a collision. -/
theorem reach_implies_held {t : Store α H K} {hs : Finset H} {f : Record α H K}
    (hct : Closed hash t) (hh : hs ⊆ digests hash t) (hreach : Reach hash t hs (hash f)) :
    f ∈ t ∨ CollisionIn hash (insert f t) := by
  obtain ⟨r, hr, he⟩ := complete_of_closed hash hct hh _ hreach
  by_cases hrf : r = f
  · exact Or.inl (hrf ▸ hr)
  · exact Or.inr (CollisionIn.of_mem hash (Finset.mem_insert_of_mem hr)
      (Finset.mem_insert_self f t) hrf he)

example : Toy.r0 ∈ ({Toy.r0, Toy.r1} : Store ℕ ℕ Unit) ∨
    CollisionIn Toy.hash (insert Toy.r0 {Toy.r0, Toy.r1}) :=
  reach_implies_held Toy.hash (hs := {1}) (by decide) (by decide) (by decide)

/-! ## Accept-built stores and salvage -/

/-- `s` is **accept-built**: some list of exactly the records of `s`, accepted one at a time
from the empty store, accepts every one of them. This is the certificate a checked store
carries. Unlike `Closed`, it rules out cycles. -/
def AcceptBuilt (s : Store α H K) : Prop :=
  ∃ l : List (Record α H K), l.toFinset = s ∧ build hash l = s

example : AcceptBuilt Toy.hash {Toy.r0, Toy.r1} := ⟨[Toy.r0, Toy.r1], by decide, by decide⟩

/-- One round of salvage: add every record of `u` whose links all resolve in `F`. -/
def retryStep (u F : Store α H K) : Store α H K :=
  F ∪ u.filter fun r ↦ r.links ⊆ digests hash F

example : retryStep Toy.hash {Toy.r0, Toy.r1, Toy.r2} {Toy.r0} = {Toy.r0, Toy.r1} := by decide

/-- The store after `n` rounds of salvage, starting from the empty store. -/
def retryRounds (u : Store α H K) : ℕ → Store α H K
  | 0 => ∅
  | n + 1 => retryStep hash u (retryRounds u n)

-- A chain of three records needs three rounds: `u.card` rounds are exactly enough.
example : retryRounds Toy.hash {Toy.r0, Toy.r1, Toy.r2} 2 = {Toy.r0, Toy.r1} := by decide
example : retryRounds Toy.hash {Toy.r0, Toy.r1, Toy.r2} 3 = {Toy.r0, Toy.r1, Toy.r2} := by
  decide

/-- **Salvage**, "keep what verifies": accept every record of `u` whose links resolve, and
repeat. `u.card` rounds are enough: a round that changes the store adds a record of `u`. -/
def buildRetry (u : Store α H K) : Store α H K := retryRounds hash u u.card

-- The order records arrive in does not matter.
example : buildRetry Toy.hash {Toy.r2, Toy.r1, Toy.r0} = {Toy.r0, Toy.r1, Toy.r2} := by decide
-- A record whose link points to nothing is dropped, and so is a cycle.
example : buildRetry Toy.hash {Toy.r0, Toy.r2, Toy.c5, Toy.c6} = {Toy.r0} := by decide
#guard buildRetry Toy.hash {Toy.r4, Toy.r2, Toy.r1, Toy.r0, Toy.c5} =
  {Toy.r0, Toy.r1, Toy.r2, Toy.r4}

/-- Salvage rounds only take records from `u`. -/
theorem retryRounds_subset (u : Store α H K) (n : ℕ) : retryRounds hash u n ⊆ u := by
  induction n with
  | zero => exact Finset.empty_subset _
  | succ n ih => exact Finset.union_subset ih (Finset.filter_subset _ _)

/-- Salvage keeps only records it was given. -/
theorem buildRetry_subset (u : Store α H K) : buildRetry hash u ⊆ u :=
  retryRounds_subset hash u _

/-- Later rounds of salvage hold more records. -/
theorem retryRounds_mono (u : Store α H K) : Monotone (retryRounds hash u) :=
  monotone_nat_of_le_succ fun _ ↦ Finset.subset_union_left

/-- A bigger store has more hashes. -/
theorem digests_mono (h : s ⊆ t) : digests hash s ⊆ digests hash t :=
  Finset.image_subset_image h

/-- Accepting never removes a record. -/
theorem subset_accept (s : Store α H K) (r : Record α H K) : s ⊆ accept hash s r := by
  unfold accept
  split_ifs
  · exact Finset.subset_insert r s
  · exact subset_rfl

/-- Accepting adds at most the offered record. -/
theorem accept_subset_insert (s : Store α H K) (r : Record α H K) :
    accept hash s r ⊆ insert r s := by
  unfold accept
  split_ifs
  · exact subset_rfl
  · exact Finset.subset_insert r s

/-- A bigger store accepts at least as much. -/
theorem accept_mono (h : s ⊆ t) (r : Record α H K) : accept hash s r ⊆ accept hash t r := by
  by_cases hl : r.links ⊆ digests hash s
  · rw [accept_of_resolves hash hl, accept_of_resolves hash (hl.trans (digests_mono hash h))]
    exact Finset.insert_subset_insert r h
  · rw [show accept hash s r = s by simp [accept, hl]]
    exact h.trans (subset_accept hash t r)

/-- Accepting a list of records never removes a record. -/
theorem subset_foldl_accept (l : List (Record α H K)) :
    ∀ s, s ⊆ l.foldl (accept hash) s := by
  induction l with
  | nil => intro s; exact subset_rfl
  | cons r l ih => intro s; exact (subset_accept hash s r).trans (ih _)

/-- Accepting a list into a bigger store gives a bigger store. -/
theorem foldl_accept_mono (l : List (Record α H K)) :
    ∀ {s t : Store α H K}, s ⊆ t → l.foldl (accept hash) s ⊆ l.foldl (accept hash) t := by
  induction l with
  | nil => intro s t h; exact h
  | cons r l ih => intro s t h; exact ih (accept_mono hash h r)

/-- Accepting a list adds only records of the list. -/
theorem foldl_accept_subset (l : List (Record α H K)) :
    ∀ s, l.foldl (accept hash) s ⊆ s ∪ l.toFinset := by
  induction l with
  | nil => intro s; simp
  | cons r l ih =>
    intro s
    refine (ih _).trans fun x hx ↦ ?_
    rcases Finset.mem_union.mp hx with hx | hx
    · rcases Finset.mem_insert.mp (accept_subset_insert hash s r hx) with rfl | hx
      · simp
      · simp [hx]
    · simp [hx]

/-- Accepting records whose links all resolve in the starting store inserts every one. -/
theorem foldl_accept_of_resolve (l : List (Record α H K)) :
    ∀ s, (∀ r ∈ l, r.links ⊆ digests hash s) → l.foldl (accept hash) s = s ∪ l.toFinset := by
  induction l with
  | nil => intro s _; simp
  | cons r l ih =>
    intro s h
    rw [List.foldl_cons, accept_of_resolves hash (h r (by simp))]
    rw [ih _ fun x hx ↦ (h x (by simp [hx])).trans (digests_mono hash (Finset.subset_insert _ _))]
    ext x
    simp

/-- Every round of salvage is accept-built: accept the records of each round, round by round. -/
theorem acceptBuilt_retryRounds (u : Store α H K) (n : ℕ) :
    AcceptBuilt hash (retryRounds hash u n) := by
  induction n with
  | zero => exact ⟨[], by simp [retryRounds], by simp [build, retryRounds]⟩
  | succ n ih =>
    obtain ⟨l, hl, hb⟩ := ih
    refine ⟨l ++ (u.filter fun r ↦ r.links ⊆ digests hash (retryRounds hash u n)).toList, ?_, ?_⟩
    · rw [List.toFinset_append, hl, Finset.toList_toFinset]
      rfl
    · show List.foldl (accept hash) ∅ (l ++ _) = _
      rw [List.foldl_append]
      show List.foldl (accept hash) (build hash l) _ = _
      rw [hb, foldl_accept_of_resolve hash _ _
        (fun r hr ↦ (Finset.mem_filter.mp (Finset.mem_toList.mp hr)).2), Finset.toList_toFinset]
      rfl

/-- **Salvage keeps a checked store.** What `buildRetry` keeps is accept-built. -/
theorem salvage_built (u : Store α H K) : AcceptBuilt hash (buildRetry hash u) :=
  acceptBuilt_retryRounds hash u _

example : AcceptBuilt Toy.hash (buildRetry Toy.hash {Toy.r0, Toy.r2, Toy.c5, Toy.c6}) :=
  salvage_built Toy.hash _

/-- The invariant behind `salvage_maximal`: a store built by accepting records of `u` lies inside
some round of salvage no later than its size. -/
theorem foldl_accept_within (u : Store α H K) (l : List (Record α H K))
    (hlu : ∀ x ∈ l, x ∈ u) :
    ∀ B k, k ≤ B.card → B ⊆ retryRounds hash u k →
      ∃ k', k' ≤ (l.foldl (accept hash) B).card ∧
        l.foldl (accept hash) B ⊆ retryRounds hash u k' := by
  induction l with
  | nil => intro B k hk hB; exact ⟨k, hk, hB⟩
  | cons r l ih =>
    intro B k hk hB
    have hlu' : ∀ x ∈ l, x ∈ u := fun x hx ↦ hlu x (List.mem_cons_of_mem _ hx)
    rw [List.foldl_cons]
    by_cases hl : r.links ⊆ digests hash B
    · rw [accept_of_resolves hash hl]
      by_cases hrB : r ∈ B
      · rw [Finset.insert_eq_of_mem hrB]
        exact ih hlu' B k hk hB
      · refine ih hlu' (insert r B) (k + 1) (by rw [Finset.card_insert_of_notMem hrB]; omega) ?_
        have hk1 : retryRounds hash u k ⊆ retryRounds hash u (k + 1) :=
          retryRounds_mono hash u (Nat.le_succ k)
        refine Finset.insert_subset ?_ (hB.trans hk1)
        show r ∈ retryStep hash u (retryRounds hash u k)
        exact Finset.mem_union_right _
          (Finset.mem_filter.mpr ⟨hlu r (by simp), hl.trans (digests_mono hash hB)⟩)
    · rw [show accept hash B r = B by simp [accept, hl]]
      exact ih hlu' B k hk hB

/-- **Salvage loses nothing recoverable.** Every accept-built store made of records of `u` is
inside `buildRetry hash u`: salvage keeps the largest set any client could have accepted. No
collision clause is needed. -/
theorem salvage_maximal (hs : AcceptBuilt hash s) (hsu : s ⊆ u) : s ⊆ buildRetry hash u := by
  obtain ⟨l, hl, hb⟩ := hs
  have hlu : ∀ x ∈ l, x ∈ u := fun x hx ↦ hsu (hl ▸ List.mem_toFinset.mpr hx)
  obtain ⟨k, hk, hsub⟩ :=
    foldl_accept_within hash u l hlu ∅ 0 (Nat.zero_le _) (Finset.empty_subset _)
  change k ≤ (build hash l).card at hk
  change build hash l ⊆ _ at hsub
  rw [hb] at hk hsub
  exact hsub.trans (retryRounds_mono hash u (hk.trans (Finset.card_le_card hsu)))

example : ({Toy.r0, Toy.r1} : Store ℕ ℕ Unit) ⊆
    buildRetry Toy.hash {Toy.r0, Toy.r1, Toy.r2, Toy.c5, Toy.c6} :=
  salvage_maximal Toy.hash (⟨[Toy.r0, Toy.r1], by decide, by decide⟩) (by decide)

/-- A store is accept-built exactly when salvage keeps all of it. This makes `AcceptBuilt`
decidable. -/
theorem acceptBuilt_iff : AcceptBuilt hash s ↔ buildRetry hash s = s := by
  constructor
  · intro h
    exact (buildRetry_subset hash s).antisymm (salvage_maximal hash h subset_rfl)
  · intro h
    have := salvage_built hash s
    rwa [h] at this

instance (s : Store α H K) : Decidable (AcceptBuilt hash s) :=
  decidable_of_iff _ (acceptBuilt_iff hash).symm

-- A cycle is closed (every link resolves), but no order can accept it.
example : Closed Toy.hash {Toy.c5, Toy.c6} := by decide
example : ¬ AcceptBuilt Toy.hash {Toy.c5, Toy.c6} := by decide
-- A record whose link points to nothing is not accept-built.
example : ¬ AcceptBuilt Toy.hash {Toy.r1} := by decide

/-- **Merging keeps a store checked.** The union of two accept-built stores is accept-built
(accept the records of `s` first, then those of `t`). No collision clause is needed. -/
theorem acceptBuilt_union (hs : AcceptBuilt hash s) (ht : AcceptBuilt hash t) :
    AcceptBuilt hash (s ∪ t) := by
  obtain ⟨ls, hls, hbs⟩ := hs
  obtain ⟨lt, hlt, hbt⟩ := ht
  refine ⟨ls ++ lt, by rw [List.toFinset_append, hls, hlt], ?_⟩
  have hb : build hash (ls ++ lt) = lt.foldl (accept hash) s := by
    show List.foldl (accept hash) ∅ (ls ++ lt) = _
    rw [List.foldl_append]
    show List.foldl (accept hash) (build hash ls) lt = _
    rw [hbs]
  rw [hb]
  refine Finset.Subset.antisymm ?_ (Finset.union_subset (subset_foldl_accept hash lt s) ?_)
  · rw [← hlt]
    exact foldl_accept_subset hash lt s
  · rw [← hbt]
    exact foldl_accept_mono hash lt (Finset.empty_subset s)

example : AcceptBuilt Toy.hash ({Toy.r0, Toy.r1} ∪ {Toy.r0, Toy.r3}) :=
  acceptBuilt_union Toy.hash (by decide) (by decide)

/-- **Accepting keeps a store checked.** Adding a record whose links resolve to an accept-built
store gives an accept-built store. (When the links do not resolve, `accept` changes nothing.) -/
theorem acceptBuilt_insert {r : Record α H K} (hs : AcceptBuilt hash s)
    (hl : r.links ⊆ digests hash s) : AcceptBuilt hash (insert r s) := by
  obtain ⟨l, hl', hb⟩ := hs
  refine ⟨l ++ [r], ?_, ?_⟩
  · rw [List.toFinset_append, hl']
    ext x
    simp
  · show List.foldl (accept hash) ∅ (l ++ [r]) = _
    rw [List.foldl_append]
    show List.foldl (accept hash) (build hash l) [r] = _
    rw [hb, List.foldl_cons, List.foldl_nil]
    exact accept_of_resolves hash hl

example : AcceptBuilt Toy.hash (insert Toy.r1 {Toy.r0}) :=
  acceptBuilt_insert Toy.hash (by decide) (by decide)

/-- **A checked store is fetched from its own heads.** An accept-built store holds everything
its heads reach, and nothing else. Or two records in it collide. -/
theorem fetched_build (h : AcceptBuilt hash s) :
    Fetched hash s (heads hash s) ∨ CollisionIn hash s := by
  obtain ⟨l, -, rfl⟩ := h
  exact fetched_of_build hash l

example : Fetched Toy.hash {Toy.r0, Toy.r1, Toy.r3} (heads Toy.hash {Toy.r0, Toy.r1, Toy.r3}) ∨
    CollisionIn Toy.hash {Toy.r0, Toy.r1, Toy.r3} :=
  fetched_build Toy.hash (by decide)

/-! ## Who wrote a record

Hash links show that whoever linked a record holds it. They do not show who wrote it: anyone can
make a record with any author. Only the host knows how each record arrived. A record is
**live** when Signal delivered it with the record's author as the sender, or this device sent
it. Each live message also carries a **disown** list: the hashes of records in its sender's name
that the sender did not write. The disown list is not part of the record or its hash; it is
believed only because Signal delivered it from the sender.
-/

/-- What the host knows about how records arrived. This is trusted host state. Records relayed
by another member, or imported from a dump, are simply not live. -/
structure LiveFacts (H : Type*) where
  /-- The hashes of the records that arrived live. -/
  live : Finset H
  /-- The disown lists of live records: `(d, e) ∈ disown` when the live record with hash `d`
  lists the hash `e` in its disown list. -/
  disown : Finset (H × H)
deriving DecidableEq

/-- The live records of member `a` in store `s`. -/
def liveRecords (s : Store α H K) (P : LiveFacts H) (a : K) : Store α H K :=
  s.filter fun x ↦ hash x ∈ P.live ∧ x.author = a

/-- `r` is **confirmed by its author**: some live record of `r.author` reaches `r` (a record
reaches itself), and no live record of `r.author` lists `r` in its disown list. -/
def authorConfirmed (s : Store α H K) (P : LiveFacts H) (r : Record α H K) : Prop :=
  (∃ x ∈ liveRecords hash s P r.author, Reach hash s {hash x} (hash r)) ∧
    ∀ x ∈ liveRecords hash s P r.author, (hash x, hash r) ∉ P.disown

instance (s : Store α H K) (P : LiveFacts H) (r : Record α H K) :
    Decidable (authorConfirmed hash s P r) := by
  unfold authorConfirmed; infer_instance

/-- `r` gets the **foreign marker**, "not confirmed by its author", when a live record of the
author lists it in its disown list, or when the author has a live record written at the same
time as `r` (neither reaches the other) and no live record of the author reaches `r`. It is
decided by links and disown lists, never by the order records arrived in. -/
def foreignMarked (s : Store α H K) (P : LiveFacts H) (r : Record α H K) : Prop :=
  (∃ x ∈ liveRecords hash s P r.author, (hash x, hash r) ∈ P.disown) ∨
    ((∃ x ∈ liveRecords hash s P r.author,
        ¬ Reach hash s {hash x} (hash r) ∧ ¬ Reach hash s {hash r} (hash x)) ∧
      ∀ x ∈ liveRecords hash s P r.author, ¬ Reach hash s {hash x} (hash r))

instance (s : Store α H K) (P : LiveFacts H) (r : Record α H K) :
    Decidable (foreignMarked hash s P r) := by
  unfold foreignMarked; infer_instance

/-- The members other than `r`'s author whose live records reach `r`. Each of them holds `r`
(`reach_implies_held`). -/
def holders (s : Store α H K) (P : LiveFacts H) (r : Record α H K) : Finset K :=
  (s.filter fun x ↦ hash x ∈ P.live ∧ x.author ≠ r.author ∧ Reach hash s {hash x} (hash r)).image
    Record.author

/-- The label the app shows for a record. -/
inductive Status (K : Type*) where
  /-- Confirmed by its author (`authorConfirmed`). -/
  | confirmedByAuthor
  /-- The foreign marker (`foreignMarked`). -/
  | notConfirmedByAuthor
  /-- Held by `member`, who is not its author: of the members whose live records reach it
  (`holders`), the smallest. The app shows one name, and the smallest makes the choice the
  same on every device. -/
  | heldBy (member : K)
  /-- No live record reaches it. -/
  | unconfirmed
deriving DecidableEq

/-- The **status** of record `r`, from the store and the live facts. When several labels apply,
the first wins: confirmed by author, not confirmed by author, held by, unconfirmed. So a fake in
A's name that member M links live, and that A disowns, shows "not confirmed by A", not "held by
M". "Held by" names one member: the smallest of the `holders` (for the app, the smallest ACI in
byte order). -/
def status [LinearOrder K] (s : Store α H K) (P : LiveFacts H) (r : Record α H K) : Status K :=
  if authorConfirmed hash s P r then .confirmedByAuthor
  else if foreignMarked hash s P r then .notConfirmedByAuthor
  else if h : (holders hash s P r).Nonempty then .heldBy ((holders hash s P r).min' h)
  else .unconfirmed

/-! Demo beat 5. Dave imports Bob's dump, onto which two fakes in Bob's name were added on top
of Bob's `me`. Then Alice writes `a5`, then Bob writes `b6`. Only those two arrive live. -/

-- Alice writes: the genuine history is held by Alice, her own message is confirmed, the fakes
-- stay unconfirmed.
example : liveRecords Camping.hash Camping.daveA ⟨{5}, ∅⟩ Camping.alice = {Camping.a5} := by
  decide
example : holders Camping.hash Camping.daveA ⟨{5}, ∅⟩ Camping.me = {Camping.alice} := by decide
example : status Camping.hash Camping.daveA ⟨{5}, ∅⟩ Camping.tent = .confirmedByAuthor := by
  decide
example : status Camping.hash Camping.daveA ⟨{5}, ∅⟩ Camping.me = .heldBy Camping.alice := by
  decide
example : status Camping.hash Camping.daveA ⟨{5}, ∅⟩ Camping.fake1 = .unconfirmed := by decide

-- Bob writes: his genuine message is confirmed; the fakes are marked, because `b6` is written
-- at the same time as them and does not reach them.
example : authorConfirmed Camping.hash Camping.daveB ⟨{5, 6}, ∅⟩ Camping.me := by decide
example : ¬ authorConfirmed Camping.hash Camping.daveB ⟨{5, 6}, ∅⟩ Camping.fake2 := by decide
example : foreignMarked Camping.hash Camping.daveB ⟨{5, 6}, ∅⟩ Camping.fake1 := by decide
example : ¬ foreignMarked Camping.hash Camping.daveB ⟨{5, 6}, ∅⟩ Camping.me := by decide
example : status Camping.hash Camping.daveB ⟨{5, 6}, ∅⟩ Camping.fake2 = .notConfirmedByAuthor := by
  decide
-- The same, run by the compiler rather than by the kernel.
#guard status Camping.hash Camping.daveB ⟨{5, 6}, ∅⟩ Camping.fake1 = .notConfirmedByAuthor
#guard status Camping.hash Camping.daveA ⟨{5}, ∅⟩ Camping.me = .heldBy Camping.alice
-- A disowned record is never confirmed by its author, even though the author's message
-- reaches it.
example : status Camping.hash Camping.bobStore ⟨{5, 6}, {(6, 1)}⟩ Camping.me =
    .notConfirmedByAuthor := by decide

/-- An **honest author's app**, as far as disowning goes. Member `a`'s app holds store `t`, and
`made` says which records `a` really wrote. Each live record of `a` lists in its disown list
every record in `a`'s name that it reaches in `t` and that `a` did not write. -/
def HonestAuthor (a : K) (made : Record α H K → Prop) (t : Store α H K) (P : LiveFacts H) :
    Prop :=
  ∀ x ∈ liveRecords hash t P a, ∀ f ∈ t, f.author = a → Reach hash t {hash x} (hash f) →
    ¬ made f → (hash x, hash f) ∈ P.disown

instance (a : K) (made : Record α H K → Prop) [DecidablePred made] (t : Store α H K)
    (P : LiveFacts H) : Decidable (HonestAuthor hash a made t P) := by
  unfold HonestAuthor; infer_instance

-- Beat 5: Bob's app never held the fakes (they were added to his dump on the way). It wrote
-- `me` and `b6`, and needs no disown list.
example : HonestAuthor Camping.hash Camping.bob (· ∈ ({Camping.me, Camping.b6} : Finset _))
    Camping.bobStore ⟨{5, 6}, ∅⟩ := by decide
-- If Mallory links `fake2` live (`relink`), Bob's app accepts the fakes. Its next message `b10`
-- reaches them, so an honest app must disown them.
example : ¬ HonestAuthor Camping.hash Camping.bob (· ∈ ({Camping.me, Camping.b10} : Finset _))
    Camping.relinked ⟨{9, 10}, ∅⟩ := by decide
example : HonestAuthor Camping.hash Camping.bob (· ∈ ({Camping.me, Camping.b10} : Finset _))
    Camping.relinked ⟨{9, 10}, {(10, 7), (10, 8)}⟩ := by decide
-- The order of labels: Mallory holds `fake1`, but Bob disowns it, so it shows "not confirmed
-- by Bob", not "held by Mallory". Without the disown list it would show "confirmed by Bob".
example : status Camping.hash Camping.relinked ⟨{9, 10}, {(10, 7), (10, 8)}⟩ Camping.fake1 =
    .notConfirmedByAuthor := by decide
example : status Camping.hash Camping.relinked ⟨{9, 10}, ∅⟩ Camping.fake1 =
    .confirmedByAuthor := by decide
-- Before Bob writes `b10`, only Mallory's live message reaches the fakes.
example : status Camping.hash (Camping.relinked.erase Camping.b10) ⟨{9}, ∅⟩ Camping.fake1 =
    .heldBy Camping.mallory := by decide
-- Two members hold `me`: Alice (`a5`) and Mallory (`relink` reaches it through the fakes). The
-- status names the smaller, Alice.
example : holders Camping.hash (insert Camping.relink Camping.daveA) ⟨{5, 9}, ∅⟩ Camping.me =
    {Camping.alice, Camping.mallory} := by decide
example : status Camping.hash (insert Camping.relink Camping.daveA) ⟨{5, 9}, ∅⟩ Camping.me =
    .heldBy Camping.alice := by decide

/-- **Author confirmation is sound.** Let `s` be your store and `t` the store of member `a`'s
app. Both are closed, and `a`'s app holds every live record of `a` that you hold. If `a`'s app is
honest about disowning, then every record in `a`'s name that is confirmed by its author in your
store was written by `a`. Or two records in the two stores collide. -/
theorem authorConfirmed_sound {a : K} {made : Record α H K → Prop} {P : LiveFacts H}
    (hs : Closed hash s) (ht : Closed hash t) (hheld : liveRecords hash s P a ⊆ t)
    (honest : HonestAuthor hash a made t P) {r : Record α H K} (hr : r ∈ s) (ha : r.author = a)
    (hc : authorConfirmed hash s P r) : made r ∨ CollisionIn hash (s ∪ t) := by
  obtain ⟨⟨x, hx, hreach⟩, hnot⟩ := hc
  obtain ⟨hxs, hxl, hxa⟩ := Finset.mem_filter.mp hx
  have hxlive : x ∈ liveRecords hash t P a := by
    refine Finset.mem_filter.mpr ⟨hheld (Finset.mem_filter.mpr ⟨hxs, hxl, hxa.trans ha⟩), hxl, ?_⟩
    exact hxa.trans ha
  have hxt : x ∈ t := (Finset.mem_filter.mp hxlive).1
  have hd : ∀ v : Store α H K, x ∈ v → {hash x} ⊆ digests hash v := fun v hv ↦
    Finset.singleton_subset_iff.mpr ((mem_digests hash).mpr ⟨x, hv, rfl⟩)
  rcases confirmed_exact hash hs ht (hd s hxs) (hd t hxt) with he | hcol
  · -- What `x` reaches in your store, it reaches in `a`'s store; there an honest app disowns
    -- every record in `a`'s name it did not write.
    by_contra hcon
    have hrt : r ∈ t ∧ Reach hash t {hash x} (hash r) :=
      (mem_reachSet hash).mp (he ▸ (mem_reachSet hash).mpr ⟨hr, hreach⟩)
    exact hnot x hx
      (honest x hxlive r hrt.1 ha hrt.2 fun hm ↦ hcon (Or.inl hm))
  · exact Or.inr (hcol.mono hash
      (Finset.union_subset_union (Finset.filter_subset _ _) (Finset.filter_subset _ _)))

-- Beat 5: `me` is confirmed by Bob in Dave's store, and Bob's honest app (which never held the
-- fakes) wrote it.
example : Camping.me ∈ ({Camping.me, Camping.b6} : Finset _) ∨
    CollisionIn Camping.hash (Camping.daveB ∪ Camping.bobStore) :=
  authorConfirmed_sound Camping.hash (a := Camping.bob) (P := ⟨{5, 6}, ∅⟩)
    (made := (· ∈ ({Camping.me, Camping.b6} : Finset _)))
    (by decide) (by decide) (by decide) (by decide) (by decide) rfl (by decide)

end Spec

/-! ## What links alone cannot do

Four concrete cases, checked by `decide`. Each is why some part of the app exists. -/

/-- **Limit 1: a withheld newest record passes every local check.** The chat is
`r0 ← r1 ← r2`. The server withholds the newest record `r2` from a phone. The phone's store
`{r0, r1}` is accept-built with no collision, which is all `open` and `accept` check, and it is
fetched from its own heads. Only its heads differ from the full chat's. Remedy: the next record
that links `r2`, or comparing heads with another member. -/
theorem withheld_tail_undetectable :
    let full : Store ℕ ℕ Unit := {Toy.r0, Toy.r1, Toy.r2}
    let phone : Store ℕ ℕ Unit := {Toy.r0, Toy.r1}
    phone ⊂ full ∧
      AcceptBuilt Toy.hash full ∧ AcceptBuilt Toy.hash phone ∧ ¬ CollisionIn Toy.hash phone ∧
      Fetched Toy.hash phone (heads Toy.hash phone) ∧
      heads Toy.hash phone ≠ heads Toy.hash full := by
  decide

/-- **Limit 2: a store whose tail was replaced by a consistent fake passes `open`.** The genuine
store is `r0 ← r1 ← r2 ← r4`. A doctored copy keeps `r0 ← r1` and replaces the rest by
`f2 ← f4`, with every link recomputed. Both are accept-built with no collision, which is all
`open` checks. Remedy: live messages (`confirmed_exact`, `status`): no member's live record
reaches the fakes. -/
theorem tail_replaced_passes_open :
    let genuine : Store ℕ ℕ Unit := {Toy.r0, Toy.r1, Toy.r2, Toy.r4}
    let doctored : Store ℕ ℕ Unit := {Toy.r0, Toy.r1, Toy.f2, Toy.f4}
    genuine ∩ doctored = {Toy.r0, Toy.r1} ∧ genuine ≠ doctored ∧
      AcceptBuilt Toy.hash genuine ∧ ¬ CollisionIn Toy.hash genuine ∧
      AcceptBuilt Toy.hash doctored ∧ ¬ CollisionIn Toy.hash doctored := by
  decide

/-- **Limit 3: "withheld" and "never existed" look the same.** The phone receives `r0` and then
Bob's live record `r2`, which links hash `1`. In world 1, Bob's app is honest and holds `r1`
(hash `1`), and the server withheld `r1` from the phone. In world 2, the server delivered
everything Bob holds, and nobody holds a record with hash `1`: Bob linked a made-up hash. The
phone receives the same records in both worlds, so it computes the same store and the same
missing hash. A gap shows that two histories differ; it does not show who is at fault. -/
theorem gap_indistinguishable :
    let bob1 : Store ℕ ℕ Unit := {Toy.r0, Toy.r1, Toy.r2}
    let toPhone1 : List Toy.R := [Toy.r0, Toy.r2]
    let bob2 : Store ℕ ℕ Unit := {Toy.r0, Toy.r2}
    let toPhone2 : List Toy.R := [Toy.r0, Toy.r2]
    -- World 1: Bob is honest, and the server withheld `r1`.
    (AcceptBuilt Toy.hash bob1 ∧ Toy.r1 ∈ bob1 ∧ Toy.r1 ∉ toPhone1) ∧
      -- World 2: the server delivered all Bob holds, and nobody holds hash `1`.
      (toPhone2.toFinset = bob2 ∧ 1 ∉ digests Toy.hash bob2) ∧
      -- The phone ends with the same store and the same missing hash.
      build Toy.hash toPhone1 = build Toy.hash toPhone2 ∧
      Toy.r2.links \ digests Toy.hash (build Toy.hash toPhone1) = {1} := by
  decide

namespace Camping

/-! The two worlds of limit 4. -/

/-- "I'm not coming", in Alice's name. Hash `2`. -/
def notComing : R := ⟨2, {1}, alice⟩

/-- Mallory's reply, which links `notComing`. Hash `3`. -/
def reply : R := ⟨3, {2}, mallory⟩

/-- World 1: Alice wrote `notComing`, then received `reply`. -/
def aliceStore1 : Store ℕ ℕ ℕ := build hash [tent, me, notComing, reply]

/-- Alice's next message in world 1 links her heads. -/
def next1 : R := ⟨4, heads hash aliceStore1, alice⟩

/-- World 2: Mallory made up the same record in Alice's name. -/
def forged : R := ⟨2, {1}, alice⟩

/-- World 2: Alice received `reply` before `forged`, which she fetched from Mallory. An app
never refuses a record in its own name, so she accepted it. -/
def aliceStore2 : Store ℕ ℕ ℕ := buildRetry hash {tent, me, reply, forged}

/-- Alice's next message in world 2 links her heads. -/
def next2 : R := ⟨4, heads hash aliceStore2, alice⟩

/-- What Alice wrote in world 1. -/
def aliceMade1 : Store ℕ ℕ ℕ := {tent, notComing, next1}

/-- What Alice wrote in world 2. -/
def aliceMade2 : Store ℕ ℕ ℕ := {tent, next2}

/-- Carol's store in world 1. The server dropped `notComing` to Carol, and Mallory relayed it. -/
def carolStore1 : Store ℕ ℕ ℕ := buildRetry hash {tent, me, reply, notComing, next1}

/-- Carol's live facts in world 1: everything but `notComing` arrived live; no disown lists. -/
def carolFacts1 : LiveFacts ℕ := ⟨{hash tent, hash me, hash reply, hash next1}, ∅⟩

/-- Carol's store in world 2. Mallory relayed `forged`. -/
def carolStore2 : Store ℕ ℕ ℕ := buildRetry hash {tent, me, reply, forged, next2}

/-- Carol's live facts in world 2. -/
def carolFacts2 : LiveFacts ℕ := ⟨{hash tent, hash me, hash reply, hash next2}, ∅⟩

end Camping

open Camping in
/-- **Limit 4: without disown lists, a relayed record's author cannot be checked.** In world 1,
Alice wrote `notComing`, the server dropped it to Carol, and Mallory's live `reply` links it. In
world 2, Mallory made up the same record in Alice's name and linked it. Carol's store and live
facts are the same in both worlds, so she must show the same label, "confirmed by Alice", and in
world 2 it is wrong. No rule on Carol's side can tell the worlds apart; only Alice's app can, by
disowning (`authorConfirmed_sound`). -/
theorem relay_attribution_indistinguishable :
    carolStore1 = carolStore2 ∧ carolFacts1 = carolFacts2 ∧
      notComing ∈ aliceMade1 ∧ forged ∉ aliceMade2 ∧
      status hash carolStore1 carolFacts1 notComing = .confirmedByAuthor := by
  decide

open Camping in
-- The remedy. In world 2 Alice's honest app disowns `forged` in its next message. Carol then
-- shows "not confirmed by Alice", and Alice's app meets `HonestAuthor`.
example : status hash carolStore2 ⟨carolFacts2.live, {(hash next2, hash forged)}⟩ forged =
    .notConfirmedByAuthor := by decide

open Camping in
example : HonestAuthor hash alice (· ∈ aliceMade2) (insert next2 aliceStore2)
    ⟨carolFacts2.live, {(hash next2, hash forged)}⟩ := by decide

open Camping in
-- Without the disown list, Alice's app in world 2 is not honest: `next2` reaches `forged`.
example : ¬ HonestAuthor hash alice (· ∈ aliceMade2) (insert next2 aliceStore2) carolFacts2 := by
  decide

open Camping in
-- In world 1, Alice's app is honest with no disown list, and `authorConfirmed_sound` applies.
example : notComing ∈ aliceMade1 ∨ CollisionIn hash (carolStore1 ∪ insert next1 aliceStore1) :=
  authorConfirmed_sound hash (a := alice) (made := (· ∈ aliceMade1)) (P := carolFacts1)
    (by decide) (by decide) (by decide) (by decide) (by decide) rfl (by decide)

end Crdt.Merkle
