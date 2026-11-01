/-
Copyright (c) 2026 zrdt contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: zrdt contributors
-/
import Mathlib
import Crdt.Merkle.Classify

set_option linter.unusedSectionVars false

/-!
# The fast `classify` computes the spec's status (docs/PLAN.md §3.2, `classify_spec`)

`Classify.lean` shows that the literal reference `classifyRef` computes the spec's status. This
file shows the same for `classify`, the one `zrdtd` runs, step by step:

* accept-built stores with no collision have no cycles (`acyclic_of_acceptBuilt`);
* `linkedBy` holds, for each stored digest, the stored records that link it; `reachersOf` walks
  them backwards and finds exactly the records that reach a digest;
* `authorViews` holds, for each author with a stored live record, what those records reach, what
  they disown, and the records that reach all of them;
* `authors.find?` picks the smallest holder, as the authors are sorted.
-/

namespace Crdt.Merkle

variable {α H K : Type*} [DecidableEq α] [DecidableEq H] [DecidableEq K]
variable (hash : Record α H K → H)

/-! ## Reaching, and cycles -/

/-- Reaching is transitive: what `b` reaches, `a` reaches, if `a` reaches `b`. -/
theorem Reach.trans {s : Store α H K} {a b d : H} (hab : Reach hash s {a} b)
    (hbd : Reach hash s {b} d) : Reach hash s {a} d :=
  hbd.lift hash subset_rfl (fun x hx => by rw [Finset.mem_singleton] at hx; subst hx; exact hab)

/-- Reaching from a set is reaching from one of its members. -/
theorem reach_iff_exists {s : Store α H K} {S : Finset H} {d : H} :
    Reach hash s S d ↔ ∃ a ∈ S, Reach hash s {a} d := by
  constructor
  · intro h
    induction h with
    | head hd => exact ⟨_, hd, .head (Finset.mem_singleton_self _)⟩
    | link hr _ hl ih =>
      obtain ⟨a, ha, h⟩ := ih
      exact ⟨a, ha, .link hr h hl⟩
  · rintro ⟨a, ha, h⟩
    exact h.lift hash subset_rfl (fun x hx => by
      rw [Finset.mem_singleton] at hx; subst hx; exact .head ha)

/-- `s` has **no cycles**: following one or more links from a record never leads back to its own
hash. -/
def Acyclic (s : Store α H K) : Prop :=
  ∀ x ∈ s, ∀ k ∈ x.links, ¬ Reach hash s {k} (hash x)

example : Acyclic Toy.hash (∅ : Store ℕ ℕ Unit) := by simp [Acyclic]

/-- If no record of `insert r S` links `hash r`, then reaching from any other hash in
`insert r S` never passes through `r`: it is reaching in `S`. -/
private theorem reach_insert_of_unlinked {S : Store α H K} {r : Record α H K}
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

/-- Accepting a record keeps a closed store acyclic, if the result has no collision. -/
theorem acyclic_accept {S : Store α H K} (hc : Closed hash S) (ha : Acyclic hash S)
    (r : Record α H K) (hnc : ¬ CollisionIn hash (accept hash S r)) :
    Acyclic hash (accept hash S r) := by
  unfold accept at hnc ⊢
  split_ifs at hnc ⊢ with hl
  swap
  · exact ha
  by_cases hrS : r ∈ S
  · rwa [Finset.insert_eq_of_mem hrS]
  -- No record links `hash r`: such a link resolves in `S`, so `r` would collide with a record
  -- of `S`.
  have hun : ∀ y ∈ insert r S, hash r ∉ y.links := by
    intro y hy hlink
    have hd : hash r ∈ digests hash S := by
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact hl hlink
      · exact (mem_digests hash).mpr (hc y hy _ hlink)
    obtain ⟨y', hy', he⟩ := (mem_digests hash).mp hd
    have : y' = r := by
      by_contra hne
      exact hnc (CollisionIn.of_mem hash (Finset.mem_insert_of_mem hy')
        (Finset.mem_insert_self r S) hne he)
    exact hrS (this ▸ hy')
  intro x hx k hk hR
  have hkr : k ≠ hash r := fun he => hun x hx (he ▸ hk)
  obtain ⟨hR', hne⟩ := reach_insert_of_unlinked hash hun hkr hR
  rcases Finset.mem_insert.mp hx with rfl | hx
  · exact hne rfl
  · exact ha x hx k hk hR'

/-- **An accept-built store with no collision has no cycles.** -/
theorem acyclic_of_acceptBuilt {s : Store α H K} (hb : AcceptBuilt hash s)
    (hnc : ¬ CollisionIn hash s) : Acyclic hash s := by
  obtain ⟨l, -, hbuild⟩ := hb
  suffices ∀ (l : List (Record α H K)) (S : Store α H K), Closed hash S → Acyclic hash S →
      ¬ CollisionIn hash (l.foldl (accept hash) S) → Acyclic hash (l.foldl (accept hash) S) by
    rw [← hbuild]
    exact this l ∅ (closed_empty hash) (by simp [Acyclic]) (by rw [← hbuild] at hnc; exact hnc)
  intro l
  induction l with
  | nil => intro S _ ha _; exact ha
  | cons r l ih =>
    intro S hc ha hnc
    simp only [List.foldl_cons] at hnc ⊢
    apply ih _ (closed_accept hash hc r) _ hnc
    exact acyclic_accept hash hc ha r fun h =>
      hnc (CollisionIn.mono hash (subset_foldl_accept hash l _) h)

end Crdt.Merkle

namespace Zrdt

open Crdt.Merkle

/-! ## Links followed backwards -/

/-- `WalkReach` is transitive. -/
theorem WalkReach.trans {β : Type} {m : Std.ExtTreeMap Digest β compare} {next : β → List Digest}
    {a b x : Digest} (hab : WalkReach m next [a] b) (hbx : WalkReach m next [b] x) :
    WalkReach m next [a] x := by
  induction hbx with
  | start hd => rw [List.mem_singleton] at hd; subst hd; exact hab
  | step _ hk hd ih => exact .step ih hk hd

/-- One step of `linkedBy`: record `p.2`, stored under `p.1`, is added to the list of each of its
links. -/
def linkStep (m : Std.ExtTreeMap Digest (List Digest) compare) (p : Digest × Rec) :
    Std.ExtTreeMap Digest (List Digest) compare :=
  p.2.links.foldl (init := m) fun m l => m.modify l (p.1 :: ·)

example : linkStep ∅ (Examples.dig 1, Examples.first) = ∅ := rfl

/-- `linkedBy` is the fold of `linkStep` over the stored records. -/
theorem linkedBy_eq (c : CheckedStore) :
    linkedBy c = c.raw.map.toList.foldl linkStep (c.raw.map.map fun _ _ => []) := by
  rw [linkedBy, Std.ExtTreeMap.foldl_eq_foldl_toList]
  rfl

private theorem foldl_modify (d : Digest) (ls : List Digest)
    (m : Std.ExtTreeMap Digest (List Digest) compare) (k : Digest) :
    (k ∈ ls.foldl (fun m l => m.modify l (d :: ·)) m ↔ k ∈ m) ∧
    ∀ v', (ls.foldl (fun m l => m.modify l (d :: ·)) m)[k]? = some v' →
      ∃ v, m[k]? = some v ∧ ∀ x, x ∈ v' ↔ x ∈ v ∨ (x = d ∧ k ∈ ls) := by
  induction ls generalizing m with
  | nil =>
    refine ⟨Iff.rfl, fun v' h => ⟨v', h, fun x => by simp⟩⟩
  | cons l ls ih =>
    obtain ⟨ih1, ih2⟩ := ih (m.modify l (d :: ·))
    simp only [List.foldl_cons]
    refine ⟨by rw [ih1, Std.ExtTreeMap.mem_modify], fun v' hv' => ?_⟩
    obtain ⟨v1, hv1, hx⟩ := ih2 v' hv'
    rw [Std.ExtTreeMap.getElem?_modify] at hv1
    split at hv1
    · rename_i hlk
      rw [Digest.compare_eq_iff] at hlk
      subst hlk
      obtain ⟨v, hv, rfl⟩ := Option.map_eq_some_iff.mp hv1
      refine ⟨v, hv, fun x => ?_⟩
      rw [hx x]
      simp only [List.mem_cons, true_or, and_true]
      tauto
    · rename_i hlk
      rw [Digest.compare_eq_iff] at hlk
      refine ⟨v1, hv1, fun x => ?_⟩
      rw [hx x, List.mem_cons]
      constructor
      · rintro (h | ⟨rfl, h⟩)
        · exact Or.inl h
        · exact Or.inr ⟨rfl, Or.inr h⟩
      · rintro (h | ⟨rfl, rfl | h⟩)
        · exact Or.inl h
        · exact absurd rfl hlk
        · exact Or.inr ⟨rfl, h⟩

private theorem foldl_linkStep (ps : List (Digest × Rec))
    (m : Std.ExtTreeMap Digest (List Digest) compare) (k : Digest) :
    (k ∈ ps.foldl linkStep m ↔ k ∈ m) ∧
    ∀ v', (ps.foldl linkStep m)[k]? = some v' →
      ∃ v, m[k]? = some v ∧ ∀ x, x ∈ v' ↔ x ∈ v ∨ ∃ y, (x, y) ∈ ps ∧ k ∈ y.links := by
  induction ps generalizing m with
  | nil => exact ⟨Iff.rfl, fun v' h => ⟨v', h, fun x => by simp⟩⟩
  | cons p ps ih =>
    obtain ⟨ih1, ih2⟩ := ih (linkStep m p)
    have hstep := foldl_modify p.1 p.2.links.toList m k
    rw [Array.foldl_toList] at hstep
    simp only [List.foldl_cons]
    refine ⟨by rw [ih1]; exact hstep.1, fun v' hv' => ?_⟩
    obtain ⟨v1, hv1, hx⟩ := ih2 v' hv'
    obtain ⟨v, hv, hx1⟩ := hstep.2 v1 hv1
    refine ⟨v, hv, fun x => ?_⟩
    rw [hx x, hx1 x]
    simp only [Array.mem_toList_iff]
    constructor
    · rintro ((h | ⟨rfl, h⟩) | ⟨y, hy, h⟩)
      · exact Or.inl h
      · exact Or.inr ⟨p.2, List.mem_cons_self, h⟩
      · exact Or.inr ⟨y, List.mem_cons_of_mem _ hy, h⟩
    · rintro (h | ⟨y, hy, h⟩)
      · exact Or.inl (Or.inl h)
      · rcases List.mem_cons.mp hy with he | hy
        · subst he; exact Or.inl (Or.inr ⟨rfl, h⟩)
        · exact Or.inr ⟨y, hy, h⟩

/-- The keys of `linkedBy` are the stored digests. -/
theorem mem_linkedBy (c : CheckedStore) {k : Digest} : k ∈ linkedBy c ↔ k ∈ c.raw.map := by
  rw [linkedBy_eq, (foldl_linkStep _ _ k).1, Std.ExtTreeMap.mem_map]

/-- **`linkedBy` lists exactly the stored records that link a digest.** -/
theorem linkedBy_get (c : CheckedStore) {k : Digest} {v : List Digest}
    (h : (linkedBy c)[k]? = some v) {x : Digest} :
    x ∈ v ↔ ∃ y, c.raw.map[x]? = some y ∧ k ∈ y.links := by
  rw [linkedBy_eq] at h
  obtain ⟨v0, hv0, hx⟩ := (foldl_linkStep _ _ k).2 v h
  rw [Std.ExtTreeMap.getElem?_map] at hv0
  obtain ⟨_, -, rfl⟩ := Option.map_eq_some_iff.mp hv0
  rw [hx x]
  simp only [List.not_mem_nil, false_or, Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some]

/-- **`reachersOf` finds exactly the stored records that reach `d`.** -/
theorem mem_reachersOf (c : CheckedStore) {d x : Digest} :
    x ∈ reachersOf (linkedBy c) d ↔ x ∈ c.raw.map ∧ Reach hashSpec (abs c) {x} d := by
  rw [reachersOf, mem_walk_iff, mem_linkedBy]
  refine and_congr_right fun hx => ⟨fun h => ?_, fun h => ?_⟩
  · clear hx
    induction h with
    | start hd => rw [List.mem_singleton] at hd; subst hd; exact .head (Finset.mem_singleton_self _)
    | @step k x v _ hk hxv ih =>
      obtain ⟨y, hy, hky⟩ := (linkedBy_get c hk).mp hxv
      have hxy : hashRecord y = x := c.built.hash_eq x y hy
      refine Reach.trans hashSpec ?_ ih
      refine .link (r := toSpec y) (RawStore.mem_abs.mpr ⟨x, y, hy, rfl⟩) ?_
        (mem_toSpec_links.mpr hky)
      rw [hashSpec_toSpec, hxy]
      exact .head (Finset.mem_singleton_self _)
  · induction h with
    | head hd => rw [Finset.mem_singleton] at hd; subst hd; exact .start List.mem_cons_self
    | @link y d' hy _ hl ih =>
      obtain ⟨r, rfl, hr⟩ := c.built.exists_of_mem_abs hy
      rw [hashSpec_toSpec] at ih
      have hl' : d' ∈ r.links := mem_toSpec_links.mp hl
      have hd' : d' ∈ c.raw.map := c.built.closed _ r hr d' hl'
      obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp
        (Std.ExtTreeMap.mem_iff_isSome_getElem?.mp ((mem_linkedBy c).mpr hd'))
      have hrv : hashRecord r ∈ v := (linkedBy_get c hv).mpr ⟨r, hr, hl'⟩
      exact WalkReach.trans (.step (.start List.mem_cons_self) hv hrv) ih

end Zrdt
