/-
Copyright (c) 2026 zrdt contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: zrdt contributors
-/
import Mathlib
import Crdt.Merkle.Rel
import Crdt.Merkle.ClassifyFast

set_option linter.unusedSectionVars false

/-!
# Accepting, salvaging and confirming relative to a boundary (docs/JOIN_PLAN.md §7.3)

`Defs.lean` and `Chat.lean` say what a closed store does: `accept` takes a record when every link
is the digest of a stored record, `AcceptBuilt` says some order accepts every record, and
`buildRetry` is "keep what verifies". A newcomer's store has a **boundary** `B` of digests it
holds no record for (`Rel.lean`). Here are the same notions where a link may also be a digest of
`B`. With `B = ∅` each one is the closed notion (`acceptRel_empty`, `acceptBuiltRel_empty_iff`,
`buildRetryRel_empty`).

* `acceptRel B s r`: add `r` when each link is a digest of `s` or of `B` (`inView`).
* `AcceptBuiltRel B s`: some list of exactly the records of `s`, accepted one at a time relative
  to `B` from the empty store, accepts every one of them.
* `buildRetryRel B u`: accept every record of `u` whose links resolve in the store or in `B`, and
  repeat. `salvage_builtRel`, `salvage_maximalRel`: it keeps an accept-built store, and the
  largest one; `buildRetryRel_eq_of_takesIn`: it is the only accept-built part of `u` that takes
  in the rest.

**Cycles.** A closed accept-built store has no cycle (`acyclic_of_acceptBuilt`, unless two
records collide). A store with a boundary can have one without a collision: record `x` links a
boundary digest `d`, and later a record `r` with digest `d` arrives that links `x` (a
*promotion*, `core/Zrdt/RelStore.lean`). For SHA-256 this needs a record whose digest was written
into a record that its own digest depends on; nobody can produce one, but the model does not
know that. So the statements that need "no cycle" take `Acyclic` as a hypothesis, and these
lemmas give it:

* `acyclic_insertRel`: accepting a record whose digest is not a boundary digest keeps a store
  without cycles;
* `tight_of_acyclic`: a store without cycles is reachable from its heads (`Tight`), for any
  boundary.

**Confirmation.** `reach_transfer`: what a message's links reach in one store is reached in a
second store too, unless the second store holds it only below one of its boundary digests. Or two
records collide.
-/

namespace Crdt.Merkle

section RelSpec

variable {α H K : Type*} [DecidableEq α] [DecidableEq H] [DecidableEq K]
variable (hash : Record α H K → H)

/-! ## Accepting relative to a boundary -/

/-- With no boundary, the digests a view knows are the digests of its records. -/
theorem inView_empty (s : Store α H K) : inView hash s ∅ = digests hash s := by
  simp [inView]

/-- `Acyclic` is decidable: `Reach` on a finite store is. -/
instance (s : Store α H K) : Decidable (Acyclic hash s) := by
  unfold Acyclic; infer_instance

/-- A bigger store, or a bigger boundary, knows more digests. -/
theorem inView_mono {s t : Store α H K} {B C : Finset H} (h : s ⊆ t) (hB : B ⊆ C) :
    inView hash s B ⊆ inView hash t C :=
  Finset.union_subset_union (digests_mono hash h) hB

/-- Add `r` to `s` only if every link of `r` is the digest of a record of `s` or a digest of the
boundary `B`. Otherwise `s` is unchanged. -/
def acceptRel (B : Finset H) (s : Store α H K) (r : Record α H K) : Store α H K :=
  if r.links ⊆ inView hash s B then insert r s else s

-- `r2` links `1`: rejected by the empty store, taken when `1` is a boundary digest.
example : acceptRel Toy.hash ∅ ∅ Toy.r2 = ∅ := by decide
example : acceptRel Toy.hash {1} ∅ Toy.r2 = {Toy.r2} := by decide

/-- **With no boundary, `acceptRel` is `accept`.** -/
theorem acceptRel_empty : acceptRel hash (∅ : Finset H) = accept hash := by
  funext s r
  simp [acceptRel, accept, inView_empty]

/-- When the links resolve, accepting is inserting. -/
theorem acceptRel_of_resolves {B : Finset H} {s : Store α H K} {r : Record α H K}
    (hl : r.links ⊆ inView hash s B) : acceptRel hash B s r = insert r s := by
  simp [acceptRel, hl]

/-- Accepting never removes a record. -/
theorem subset_acceptRel (B : Finset H) (s : Store α H K) (r : Record α H K) :
    s ⊆ acceptRel hash B s r := by
  unfold acceptRel
  split_ifs
  · exact Finset.subset_insert r s
  · exact subset_rfl

/-- Accepting adds at most the offered record. -/
theorem acceptRel_subset_insert (B : Finset H) (s : Store α H K) (r : Record α H K) :
    acceptRel hash B s r ⊆ insert r s := by
  unfold acceptRel
  split_ifs
  · exact subset_rfl
  · exact Finset.subset_insert r s

/-- Accepting a list of records never removes a record. -/
theorem subset_foldl_acceptRel (B : Finset H) (l : List (Record α H K)) :
    ∀ s, s ⊆ l.foldl (acceptRel hash B) s := by
  induction l with
  | nil => intro s; exact subset_rfl
  | cons r l ih => intro s; exact (subset_acceptRel hash B s r).trans (ih _)

/-- Accepting records whose links all resolve in the starting store inserts every one. -/
theorem foldl_acceptRel_of_resolve (B : Finset H) (l : List (Record α H K)) :
    ∀ s, (∀ r ∈ l, r.links ⊆ inView hash s B) → l.foldl (acceptRel hash B) s = s ∪ l.toFinset := by
  induction l with
  | nil => intro s _; simp
  | cons r l ih =>
    intro s h
    rw [List.foldl_cons, acceptRel_of_resolves hash (h r (by simp))]
    rw [ih _ fun x hx ↦ (h x (by simp [hx])).trans
      (inView_mono hash (Finset.subset_insert _ _) subset_rfl)]
    ext x
    simp

/-- The store a replica builds by accepting records one at a time relative to `B`. -/
def buildRel (B : Finset H) (l : List (Record α H K)) : Store α H K :=
  l.foldl (acceptRel hash B) ∅

example : buildRel Toy.hash {1} [Toy.r2, Toy.r4] = {Toy.r2, Toy.r4} := by decide

/-- With no boundary, `buildRel` is `build`. -/
theorem buildRel_empty (l : List (Record α H K)) : buildRel hash ∅ l = build hash l := by
  simp [buildRel, build, acceptRel_empty]

/-- `s` is **accept-built relative to `B`**: some list of exactly the records of `s`, accepted one
at a time relative to `B` from the empty store, accepts every one of them. -/
def AcceptBuiltRel (B : Finset H) (s : Store α H K) : Prop :=
  ∃ l : List (Record α H K), l.toFinset = s ∧ buildRel hash B l = s

example : AcceptBuiltRel Toy.hash {1, 3} Joining.bobF := ⟨[Toy.r2, Toy.r4], by decide, by decide⟩

/-- **With no boundary, accept-built relative to it is accept-built.** -/
theorem acceptBuiltRel_empty_iff {s : Store α H K} :
    AcceptBuiltRel hash ∅ s ↔ AcceptBuilt hash s := by
  simp [AcceptBuiltRel, AcceptBuilt, buildRel_empty]

/-! ## Salvage relative to a boundary -/

/-- One round of salvage: add every record of `u` whose links all resolve in `F` or in `B`. -/
def retryStepRel (B : Finset H) (u F : Store α H K) : Store α H K :=
  F ∪ u.filter fun r ↦ r.links ⊆ inView hash F B

/-- The store after `n` rounds of salvage relative to `B`, starting from the empty store. -/
def retryRoundsRel (B : Finset H) (u : Store α H K) : ℕ → Store α H K
  | 0 => ∅
  | n + 1 => retryStepRel hash B u (retryRoundsRel B u n)

/-- **Salvage relative to a boundary**: accept every record of `u` whose links resolve in the
store or in `B`, and repeat. `u.card` rounds are enough. -/
def buildRetryRel (B : Finset H) (u : Store α H K) : Store α H K :=
  retryRoundsRel hash B u u.card

-- Bob's records over his boundary are all kept; without the boundary, nothing is.
example : buildRetryRel Toy.hash {1, 3} Joining.bobF = Joining.bobF := by decide
example : buildRetryRel Toy.hash ∅ Joining.bobF = ∅ := by decide

/-- With no boundary, salvage relative to it is `buildRetry`. -/
theorem buildRetryRel_empty (u : Store α H K) : buildRetryRel hash ∅ u = buildRetry hash u := by
  suffices ∀ n, retryRoundsRel hash ∅ u n = retryRounds hash u n from this _
  intro n
  induction n with
  | zero => rfl
  | succ n ih => simp [retryRoundsRel, retryRounds, retryStepRel, retryStep, ih, inView_empty]

/-- Salvage rounds only take records from `u`. -/
theorem retryRoundsRel_subset (B : Finset H) (u : Store α H K) (n : ℕ) :
    retryRoundsRel hash B u n ⊆ u := by
  induction n with
  | zero => exact Finset.empty_subset _
  | succ n ih => exact Finset.union_subset ih (Finset.filter_subset _ _)

/-- Salvage keeps only records it was given. -/
theorem buildRetryRel_subset (B : Finset H) (u : Store α H K) : buildRetryRel hash B u ⊆ u :=
  retryRoundsRel_subset hash B u _

/-- Later rounds of salvage hold more records. -/
theorem retryRoundsRel_mono (B : Finset H) (u : Store α H K) :
    Monotone (retryRoundsRel hash B u) :=
  monotone_nat_of_le_succ fun _ ↦ Finset.subset_union_left

/-- Every round of salvage is accept-built relative to `B`. -/
theorem acceptBuiltRel_retryRounds (B : Finset H) (u : Store α H K) (n : ℕ) :
    AcceptBuiltRel hash B (retryRoundsRel hash B u n) := by
  induction n with
  | zero => exact ⟨[], by simp [retryRoundsRel], by simp [buildRel, retryRoundsRel]⟩
  | succ n ih =>
    obtain ⟨l, hl, hb⟩ := ih
    refine ⟨l ++ (u.filter fun r ↦ r.links ⊆ inView hash (retryRoundsRel hash B u n) B).toList,
      ?_, ?_⟩
    · rw [List.toFinset_append, hl, Finset.toList_toFinset]
      rfl
    · show List.foldl (acceptRel hash B) ∅ (l ++ _) = _
      rw [List.foldl_append]
      show List.foldl (acceptRel hash B) (buildRel hash B l) _ = _
      rw [hb, foldl_acceptRel_of_resolve hash B _ _
        (fun r hr ↦ (Finset.mem_filter.mp (Finset.mem_toList.mp hr)).2), Finset.toList_toFinset]
      rfl

/-- **Salvage keeps a store accept-built relative to `B`.** -/
theorem salvage_builtRel (B : Finset H) (u : Store α H K) :
    AcceptBuiltRel hash B (buildRetryRel hash B u) :=
  acceptBuiltRel_retryRounds hash B u _

/-- The invariant behind `salvage_maximalRel`. -/
theorem foldl_acceptRel_within (B : Finset H) (u : Store α H K) (l : List (Record α H K))
    (hlu : ∀ x ∈ l, x ∈ u) :
    ∀ S k, k ≤ S.card → S ⊆ retryRoundsRel hash B u k →
      ∃ k', k' ≤ (l.foldl (acceptRel hash B) S).card ∧
        l.foldl (acceptRel hash B) S ⊆ retryRoundsRel hash B u k' := by
  induction l with
  | nil => intro S k hk hS; exact ⟨k, hk, hS⟩
  | cons r l ih =>
    intro S k hk hS
    have hlu' : ∀ x ∈ l, x ∈ u := fun x hx ↦ hlu x (List.mem_cons_of_mem _ hx)
    rw [List.foldl_cons]
    by_cases hl : r.links ⊆ inView hash S B
    · rw [acceptRel_of_resolves hash hl]
      by_cases hrS : r ∈ S
      · rw [Finset.insert_eq_of_mem hrS]
        exact ih hlu' S k hk hS
      · refine ih hlu' (insert r S) (k + 1) (by rw [Finset.card_insert_of_notMem hrS]; omega) ?_
        have hk1 : retryRoundsRel hash B u k ⊆ retryRoundsRel hash B u (k + 1) :=
          retryRoundsRel_mono hash B u (Nat.le_succ k)
        refine Finset.insert_subset ?_ (hS.trans hk1)
        show r ∈ retryStepRel hash B u (retryRoundsRel hash B u k)
        exact Finset.mem_union_right _
          (Finset.mem_filter.mpr ⟨hlu r (by simp), hl.trans (inView_mono hash hS subset_rfl)⟩)
    · rw [show acceptRel hash B S r = S by simp [acceptRel, hl]]
      exact ih hlu' S k hk hS

/-- **Salvage loses nothing recoverable.** Every store accept-built relative to `B` made of
records of `u` is inside `buildRetryRel B u`. -/
theorem salvage_maximalRel {B : Finset H} {s u : Store α H K} (hs : AcceptBuiltRel hash B s)
    (hsu : s ⊆ u) : s ⊆ buildRetryRel hash B u := by
  obtain ⟨l, hl, hb⟩ := hs
  have hlu : ∀ x ∈ l, x ∈ u := fun x hx ↦ hsu (hl ▸ List.mem_toFinset.mpr hx)
  obtain ⟨k, hk, hsub⟩ :=
    foldl_acceptRel_within hash B u l hlu ∅ 0 (Nat.zero_le _) (Finset.empty_subset _)
  change k ≤ (buildRel hash B l).card at hk
  change buildRel hash B l ⊆ _ at hsub
  rw [hb] at hk hsub
  exact hsub.trans (retryRoundsRel_mono hash B u (hk.trans (Finset.card_le_card hsu)))

/-- Every round of salvage stays inside a store `E` that takes in `u` relative to `B`. -/
theorem retryRoundsRel_subset_of_takesIn {B : Finset H} {u E : Store α H K}
    (hE : ∀ r ∈ u, r.links ⊆ inView hash E B → r ∈ E) (n : ℕ) :
    retryRoundsRel hash B u n ⊆ E := by
  induction n with
  | zero => simp [retryRoundsRel]
  | succ n ih =>
    intro r hr
    simp only [retryRoundsRel, retryStepRel, Finset.mem_union, Finset.mem_filter] at hr
    rcases hr with hr | ⟨hru, hl⟩
    · exact ih hr
    · exact hE r hru (hl.trans (inView_mono hash ih subset_rfl))

/-- **Salvage is inside every store that takes in `u`** relative to `B`. -/
theorem buildRetryRel_subset_of_takesIn {B : Finset H} {u E : Store α H K}
    (hE : ∀ r ∈ u, r.links ⊆ inView hash E B → r ∈ E) : buildRetryRel hash B u ⊆ E :=
  retryRoundsRel_subset_of_takesIn hash hE _

/-- **Salvage, characterised.** A part `E` of `u` that is accept-built relative to `B` and takes
in `u` relative to `B` is exactly what salvage keeps. -/
theorem buildRetryRel_eq_of_takesIn {B : Finset H} {u E : Store α H K} (hsub : E ⊆ u)
    (hb : AcceptBuiltRel hash B E) (hE : ∀ r ∈ u, r.links ⊆ inView hash E B → r ∈ E) :
    buildRetryRel hash B u = E :=
  (buildRetryRel_subset_of_takesIn hash hE).antisymm (salvage_maximalRel hash hb hsub)

example : buildRetryRel Toy.hash {1, 3} Joining.bobF = Joining.bobF :=
  buildRetryRel_eq_of_takesIn Toy.hash subset_rfl ⟨[Toy.r2, Toy.r4], by decide, by decide⟩
    (by decide)

/-- **An accept-built set is inside every store that takes it in**, relative to `B`. -/
theorem subset_of_takesInRel {B : Finset H} {u E : Store α H K} (hu : AcceptBuiltRel hash B u)
    (hE : ∀ r ∈ u, r.links ⊆ inView hash E B → r ∈ E) : u ⊆ E :=
  (salvage_maximalRel hash hu subset_rfl).trans (buildRetryRel_subset_of_takesIn hash hE)

/-! ## Heads, closedness and cycles -/

/-- In a view that is closed relative to its boundary, everything reachable from the view's heads
is a digest the view knows. -/
theorem reach_mem_inView {S : Store α H K} {B : Finset H} (hS : ClosedRel hash S B)
    {d : H} (h : Reach hash S (headsRel hash S B) d) : d ∈ inView hash S B := by
  cases h with
  | head h => exact ((mem_headsRel hash).mp h).1
  | link hr _ hl => exact hS _ hr hl

/-- **A store without cycles is reachable from its heads**, for any boundary: every record of
`S` is reached from `headsRel S B`. -/
theorem tight_of_acyclic {S : Store α H K} (B : Finset H) (hac : Acyclic hash S) :
    Tight hash S (headsRel hash S B) := by
  classical
  -- The records of `S` from which `d` is reached through at least one link.
  let A : H → Finset (Record α H K) := fun d =>
    S.filter fun y => ∃ k ∈ y.links, Reach hash S {k} d
  suffices key : ∀ n, ∀ x ∈ S, (A (hash x)).card = n → Reach hash S (headsRel hash S B) (hash x)
    from fun x hx => key _ x hx rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro x hx hn
    by_cases hl : hash x ∈ linksOf S
    · obtain ⟨y, hy, hxy⟩ := mem_linksOf.mp hl
      have hlt : (A (hash y)).card < (A (hash x)).card := by
        apply Finset.card_lt_card
        rw [Finset.ssubset_iff_of_subset]
        · refine ⟨y, Finset.mem_filter.mpr ⟨hy, hash x, hxy, .head (Finset.mem_singleton_self _)⟩,
            fun hmem => ?_⟩
          obtain ⟨-, k, hk, hR⟩ := Finset.mem_filter.mp hmem
          exact hac y hy k hk hR
        · intro z hz
          obtain ⟨hz, k, hk, hR⟩ := Finset.mem_filter.mp hz
          exact Finset.mem_filter.mpr ⟨hz, k, hk, Reach.trans hash hR
            (.link hy (.head (Finset.mem_singleton_self _)) hxy)⟩
      exact .link hy (ih _ (hn ▸ hlt) y hy rfl) hxy
    · exact .head ((mem_headsRel hash).mpr
        ⟨(mem_inView hash).mpr (.inl ⟨x, hx, rfl⟩), hl⟩)

example : Tight Toy.hash Joining.bobS (headsRel Toy.hash Joining.bobS Joining.bobB) :=
  tight_of_acyclic Toy.hash _ (by decide)

/-- If no record of `insert r S` links `hash r`, then reaching from any other hash in
`insert r S` never passes through `r`: it is reaching in `S`. -/
theorem reach_insert_of_unlinked' {S : Store α H K} {r : Record α H K}
    (hun : ∀ y ∈ insert r S, hash r ∉ y.links) {k d : H} (hk : k ≠ hash r)
    (h : Reach hash (insert r S) {k} d) : Reach hash S {k} d ∧ d ≠ hash r := by
  induction h with
  | head hd =>
    rw [Finset.mem_singleton] at hd
    subst hd
    exact ⟨.head (Finset.mem_singleton_self _), hk⟩
  | @link y d hy _ hl ih =>
    obtain ⟨ih, hne⟩ := ih
    have hyS : y ∈ S := by
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact absurd rfl hne
      · exact hy
    exact ⟨.link hyS ih hl, fun he => hun y (Finset.mem_insert_of_mem hyS) (he ▸ hl)⟩

/-- **Accepting a record whose digest is new keeps a store without cycles**, relative to a
boundary: the record's links resolve in `S` or in `B`, and its digest is neither a digest of `S`
nor a digest of `B`. (A record whose digest is a boundary digest is the one case left out: see
the module header.) -/
theorem acyclic_insertRel {S : Store α H K} {B : Finset H} (hS : ClosedRel hash S B)
    (ha : Acyclic hash S) {r : Record α H K} (hl : r.links ⊆ inView hash S B)
    (hB : hash r ∉ B) (hd : hash r ∉ digests hash S) : Acyclic hash (insert r S) := by
  have hnot : hash r ∉ inView hash S B := fun h =>
    ((mem_inView hash).mp h).elim (fun h' => hd ((mem_digests hash).mpr h')) hB
  have hun : ∀ y ∈ insert r S, hash r ∉ y.links := by
    intro y hy hlink
    rcases Finset.mem_insert.mp hy with rfl | hy
    · exact hnot (hl hlink)
    · exact hnot (hS y hy hlink)
  intro x hx k hk hR
  have hkr : k ≠ hash r := fun he => hun x hx (he ▸ hk)
  obtain ⟨hR', hne⟩ := reach_insert_of_unlinked' hash hun hkr hR
  rcases Finset.mem_insert.mp hx with rfl | hx
  · exact hne rfl
  · exact ha x hx k hk hR'

/-- A cycle with no collision, in a store with a boundary: `x` links the boundary digest `1`, and
`y`, whose digest is `1`, links `x`. Each record's links resolve when it is accepted (`x` first,
relative to the boundary `{1}`), and the two records have different digests. -/
theorem promoted_cycle :
    let x : Toy.R := ⟨2, {1}, ()⟩
    let y : Toy.R := ⟨1, {2}, ()⟩
    buildRel Toy.hash {1} [x, y] = {x, y} ∧ ¬ CollisionIn Toy.hash {x, y} ∧
      ¬ Acyclic Toy.hash {x, y} := by
  refine ⟨by decide, by decide, fun h => ?_⟩
  exact h ⟨2, {1}, ()⟩ (by simp) 1 (by simp)
    (.link (r := ⟨1, {2}, ()⟩) (by simp) (.head (by decide)) (by decide))

/-- **Why the statements that need it assume no cycle.** The two records of `promoted_cycle` are
each linked by the other, so neither is a head and neither is reachable from the heads: the store
is accept-built relative to its boundary, has no collision, and is not `Tight`. -/
theorem promoted_cycle_not_tight :
    let x : Toy.R := ⟨2, {1}, ()⟩
    let y : Toy.R := ⟨1, {2}, ()⟩
    AcceptBuiltRel Toy.hash {1} {x, y} ∧ ¬ CollisionIn Toy.hash {x, y} ∧
      ¬ Tight Toy.hash {x, y} (headsRel Toy.hash {x, y} {1}) := by
  refine ⟨⟨[⟨2, {1}, ()⟩, ⟨1, {2}, ()⟩], by decide, by decide⟩, by decide, fun h => ?_⟩
  have hh : headsRel Toy.hash ({⟨2, {1}, ()⟩, ⟨1, {2}, ()⟩} : Store ℕ ℕ Unit) {1} = ∅ := by
    decide
  have := h ⟨2, {1}, ()⟩ (by simp)
  rw [hh] at this
  exact absurd (Reach.mem_of_bound Toy.hash (R := ∅) subset_rfl (by simp) this) (by simp)

/-! ## Confirmation relative to a boundary -/

/-- In a view closed relative to its boundary, reaching from digests of its records gives digests
the view knows. -/
theorem reach_mem_inView_of {T : Store α H K} {BT : Finset H} (hT : ClosedRel hash T BT)
    {hs : Finset H} (hsT : hs ⊆ digests hash T) {d : H} (h : Reach hash T hs d) :
    d ∈ inView hash T BT := by
  cases h with
  | head h => exact (mem_inView hash).mpr (.inl ((mem_digests hash).mp (hsT h)))
  | link hr _ hl => exact hT _ hr hl

/-- **What the links reach carries over to a second store, up to its boundary.** A message links
the digests `hs`, all digests of records of `T`, a view closed relative to its boundary `BT`.
Each digest reachable from `hs` through the records of `S` is reachable from `hs` through the
records of `T`; or the path in `S` passes a digest `b` that `T` knows only as a boundary digest,
reachable from `hs` in `T`, and `S` reaches the digest from `b`. Or two records of `S ∪ T`
collide. -/
theorem reach_transfer {S T : Store α H K} {BT : Finset H} (hT : ClosedRel hash T BT)
    {hs : Finset H} (hsT : hs ⊆ digests hash T) :
    (∀ d, Reach hash S hs d → Reach hash T hs d ∨
      ∃ b, b ∈ BT ∧ b ∉ digests hash T ∧ Reach hash T hs b ∧ Reach hash S {b} d) ∨
      CollisionIn hash (S ∪ T) := by
  by_cases hc : CollisionIn hash (S ∪ T)
  · exact .inr hc
  refine .inl fun d hd => ?_
  induction hd with
  | head h => exact .inl (.head h)
  | @link r d hr _ hl ih =>
    rcases ih with hRT | ⟨b, hb, hbn, hRb, hRS⟩
    · rcases (mem_inView hash).mp (reach_mem_inView_of hash hT hsT hRT) with ⟨r', hr', he⟩ | hb
      · by_cases hrr : r' = r
        · subst hrr
          exact .inl (.link hr' hRT hl)
        · exact absurd (CollisionIn.of_mem hash (Finset.mem_union_right S hr')
            (Finset.mem_union_left T hr) hrr he) hc
      · by_cases hrT : hash r ∈ digests hash T
        · obtain ⟨r', hr', he⟩ := (mem_digests hash).mp hrT
          by_cases hrr : r' = r
          · subst hrr
            exact .inl (.link hr' hRT hl)
          · exact absurd (CollisionIn.of_mem hash (Finset.mem_union_right S hr')
              (Finset.mem_union_left T hr) hrr he) hc
        · exact .inr ⟨hash r, hb, hrT, hRT, .link hr (.head (Finset.mem_singleton_self _)) hl⟩
    · exact .inr ⟨b, hb, hbn, hRb, .link hr hRS hl⟩

-- Alice's whole store against Bob's view: a message linking `4` reaches `0` in Alice's store,
-- through `1`, which Bob holds only as a boundary digest.
example : (∀ d, Reach Toy.hash Joining.alice {4} d → Reach Toy.hash Joining.bobF {4} d ∨
      ∃ b, b ∈ Joining.bobB ∧ b ∉ digests Toy.hash Joining.bobF ∧
        Reach Toy.hash Joining.bobF {4} b ∧ Reach Toy.hash Joining.alice {b} d) ∨
    CollisionIn Toy.hash (Joining.alice ∪ Joining.bobF) :=
  reach_transfer Toy.hash (by decide) (by decide)

end RelSpec

end Crdt.Merkle
