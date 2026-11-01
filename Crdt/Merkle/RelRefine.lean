/-
Copyright (c) 2026 zrdt contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: zrdt contributors
-/
import Mathlib
import Crdt.Merkle.RelBridge
import Crdt.Merkle.LoadApi

set_option linter.unusedSectionVars false

/-!
# A store with a boundary, seen in the spec model (docs/JOIN_PLAN.md §7.3)

`Refine.lean` and `LoadApi.lean` say what each operation of a closed store (`CheckedStore`) does
to `abs c`. This file does the same for a store with a boundary (`RelStore`,
`core/Zrdt/RelStore.lean`): `c.raw.abs` is the set of its stored records in the spec model, and
`boundarySet c.boundary` is its boundary, the digests it took without a record. Every statement
here, with an empty boundary, says what the closed statement says (`inView_empty`,
`headsRel_empty`, `acceptRel_empty`, `acceptBuiltRel_empty_iff`, `buildRetryRel_empty`).

* Observers: `mem_heads_iff` (the head cache is `headsRel`), `closedRel` (every link is a stored
  digest or a boundary digest), `no_collision_model`.
* `fetched_model`: every digest reachable from the heads is stored or a boundary digest, and,
  when the store has no cycle, every stored record is reachable from the heads.
  `acyclic_of_unpromoted`: a store none of whose records has a boundary digest as its digest has
  no cycle.
* `agree_model`: two stores with the same heads hold the same records, when neither holds a
  record whose digest the other has only as a boundary digest, and neither has a cycle. Or two
  records collide.
* `accept_means` (read by `AcceptRelMeans`): what each result of `accept` means.
* `merge_model`: a merged store holds the records of both, and knows the digests both know.
* `load_iff_model`: when `load` (`OPEN` of a relative blob) gives a store, and which.
* `salvage_model`: what `salvage` keeps (`buildRetryRel`) and drops.
* `confirmed_model`: what a message's links reach in your store is reached in the sender's store
  too, except below a digest the sender has only as a boundary digest. Or two records collide.
-/

namespace Zrdt

open Crdt.Merkle

/-! ## Accept orders, in the spec model -/

/-- Accepting the records of an accept order relative to `B` oldest first, in the spec model,
accepts every one of them. -/
theorem AcceptOrderRel.buildRel_eq {B : Boundary} {l : List Rec} (h : AcceptOrderRel B l) :
    buildRel hashSpec (boundarySet B) (l.reverse.map toSpec) = (l.map toSpec).toFinset := by
  induction h with
  | nil => rfl
  | @cons r older hr _ ih =>
    show List.foldl (acceptRel hashSpec (boundarySet B)) ∅ ((r :: older).reverse.map toSpec) = _
    rw [List.reverse_cons, List.map_append, List.foldl_append]
    change List.foldl (acceptRel hashSpec (boundarySet B))
      (buildRel hashSpec (boundarySet B) (older.reverse.map toSpec)) _ = _
    rw [ih, List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil, List.map_cons,
      List.toFinset_cons]
    apply acceptRel_of_resolves
    intro d hd
    have hd' : d ∈ r.links := by simpa [toSpec] using hd
    rw [mem_inView]
    rcases hr d hd' with hb | ⟨r', hr', rfl⟩
    · exact .inr (mem_boundarySet.mpr hb)
    · exact .inl ⟨toSpec r', List.mem_toFinset.mpr (List.mem_map_of_mem hr'), hashSpec_toSpec r'⟩

/-- The spec records of an accept order relative to `B` are accept-built relative to it. -/
theorem AcceptOrderRel.acceptBuiltRel {B : Boundary} {l : List Rec} (h : AcceptOrderRel B l) :
    AcceptBuiltRel hashSpec (boundarySet B) (l.map toSpec).toFinset :=
  ⟨l.reverse.map toSpec, by ext x; simp, h.buildRel_eq⟩

/-! ## The bridge from `BuiltRel` -/

namespace BuiltRel

variable {c : RawStore} {B : Boundary}

/-- A stored record, by digest: stored under `k` exactly when its spec record is in the store
and `k` is its digest. -/
theorem getElem?_eq_some_iff (h : BuiltRel c B) {k : Digest} {r : Rec} :
    c.map[k]? = some r ↔ toSpec r ∈ c.abs ∧ hashRecord r = k := by
  constructor
  · intro hk
    exact ⟨RawStore.mem_abs.mpr ⟨k, r, hk, rfl⟩, h.hash_eq k r hk⟩
  · rintro ⟨hr, rfl⟩
    obtain ⟨k, r', hk, he⟩ := RawStore.mem_abs.mp hr
    obtain rfl := toSpec_injective he
    rw [h.hash_eq k _ hk]
    exact hk

/-- Every spec record of the store is the spec record of a record stored under its digest. -/
theorem exists_of_mem_abs (h : BuiltRel c B) {x : SpecRec} (hx : x ∈ c.abs) :
    ∃ r, toSpec r = x ∧ c.map[hashRecord r]? = some r := by
  obtain ⟨k, r, hk, rfl⟩ := RawStore.mem_abs.mp hx
  exact ⟨r, rfl, by rwa [h.hash_eq k r hk]⟩

/-- A digest is stored exactly when the spec store holds a record with that digest. -/
theorem mem_digests_abs (h : BuiltRel c B) {d : Digest} :
    d ∈ digests hashSpec c.abs ↔ d ∈ c.map := by
  rw [mem_digests, Std.ExtTreeMap.mem_iff_isSome_getElem?, Option.isSome_iff_exists]
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨k, r, hk, rfl⟩ := RawStore.mem_abs.mp hx
    rw [hashSpec_toSpec, h.hash_eq k r hk]
    exact ⟨r, hk⟩
  · rintro ⟨r, hr⟩
    exact ⟨toSpec r, RawStore.mem_abs.mpr ⟨d, r, hr, rfl⟩,
      by rw [hashSpec_toSpec, h.hash_eq d r hr]⟩

/-- The digests the view knows are the stored digests and the boundary digests. -/
theorem mem_inView (h : BuiltRel c B) {d : Digest} :
    d ∈ inView hashSpec c.abs (boundarySet B) ↔ d ∈ c.map ∨ d ∈ B := by
  rw [Crdt.Merkle.inView, Finset.mem_union, h.mem_digests_abs, mem_boundarySet]

/-- **No collision**: two different stored records never have the same digest. -/
theorem no_collision (h : BuiltRel c B) : ¬ CollisionIn hashSpec c.abs := by
  rintro ⟨x, hx, y, hy, hne, heq⟩
  obtain ⟨k, r, hk, rfl⟩ := RawStore.mem_abs.mp hx
  obtain ⟨k', r', hk', rfl⟩ := RawStore.mem_abs.mp hy
  rw [hashSpec_toSpec, hashSpec_toSpec] at heq
  have e₁ := h.hash_eq k r hk
  have e₂ := h.hash_eq k' r' hk'
  subst e₁ e₂
  rw [heq, hk'] at hk
  cases hk
  exact hne rfl

/-- **The head cache is `headsRel`**: the stored digests and boundary digests no record links. -/
theorem mem_heads_iff (h : BuiltRel c B) {d : Digest} :
    d ∈ c.heads ↔ d ∈ headsRel hashSpec c.abs (boundarySet B) := by
  rw [h.heads_iff, mem_headsRel, h.mem_inView, mem_linksOf]
  refine and_congr_right fun _ => ⟨fun hn ⟨x, hx, hl⟩ => ?_, fun hn k r hk hl => ?_⟩
  · obtain ⟨k, r, hk, rfl⟩ := RawStore.mem_abs.mp hx
    exact hn k r hk (mem_toSpec_links.mp hl)
  · exact hn ⟨toSpec r, RawStore.mem_abs.mpr ⟨k, r, hk, rfl⟩, mem_toSpec_links.mpr hl⟩

/-- **Closed relative to the boundary**: every link is a stored digest or a boundary digest. -/
theorem closedRel (h : BuiltRel c B) : ClosedRel hashSpec c.abs (boundarySet B) := by
  intro x hx d hd
  obtain ⟨k, r, hk, rfl⟩ := RawStore.mem_abs.mp hx
  exact h.mem_inView.mpr (h.closed k r hk d (mem_toSpec_links.mp hd))

/-- The spec store is the set of the records of the accept order. -/
theorem abs_eq_order (_h : BuiltRel c B) {l : List Rec}
    (hmem : ∀ r, r ∈ l ↔ ∃ k : Digest, c.map[k]? = some r) : c.abs = (l.map toSpec).toFinset := by
  ext x
  rw [RawStore.mem_abs, List.mem_toFinset, List.mem_map]
  constructor
  · rintro ⟨k, r, hk, rfl⟩
    exact ⟨r, (hmem r).mpr ⟨k, hk⟩, rfl⟩
  · rintro ⟨r, hr, rfl⟩
    obtain ⟨k, hk⟩ := (hmem r).mp hr
    exact ⟨k, r, hk, rfl⟩

/-- **Accept-built relative to the boundary.** -/
theorem acceptBuiltRel (h : BuiltRel c B) : AcceptBuiltRel hashSpec (boundarySet B) c.abs := by
  obtain ⟨l, hl, hmem⟩ := h.order
  rw [h.abs_eq_order hmem]
  exact hl.acceptBuiltRel

/-- **No cycle, when no record was promoted.** If no stored record has a boundary digest as its
digest, the store has no cycle. -/
theorem acyclic_of_unpromoted (h : BuiltRel c B) (hp : ∀ d ∈ B, d ∉ c.map) :
    Acyclic hashSpec c.abs := by
  obtain ⟨l, hl, hmem⟩ := h.order
  rw [h.abs_eq_order hmem]
  have hstored : ∀ r ∈ l, c.map[hashRecord r]? = some r := fun r hr => by
    obtain ⟨k, hk⟩ := (hmem r).mp hr
    rwa [h.hash_eq k r hk]
  clear hmem
  induction hl with
  | nil => simp [Acyclic]
  | @cons r older hr hold ih =>
    have ih := ih fun x hx => hstored x (List.mem_cons_of_mem _ hx)
    rw [List.map_cons, List.toFinset_cons]
    by_cases hin : toSpec r ∈ (older.map toSpec).toFinset
    · rwa [Finset.insert_eq_of_mem hin]
    have hsr := hstored r List.mem_cons_self
    refine acyclic_insertRel hashSpec (B := boundarySet B) ?_ ih ?_ ?_ ?_
    · intro x hx d hd
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hx)
      rw [Crdt.Merkle.mem_inView]
      rcases hold.links y hy d (mem_toSpec_links.mp hd) with hb | ⟨y', hy', rfl⟩
      · exact .inr (mem_boundarySet.mpr hb)
      · exact .inl ⟨toSpec y', List.mem_toFinset.mpr (List.mem_map_of_mem hy'), hashSpec_toSpec y'⟩
    · intro d hd
      rw [Crdt.Merkle.mem_inView]
      rcases hr d (mem_toSpec_links.mp hd) with hb | ⟨y', hy', rfl⟩
      · exact .inr (mem_boundarySet.mpr hb)
      · exact .inl ⟨toSpec y', List.mem_toFinset.mpr (List.mem_map_of_mem hy'), hashSpec_toSpec y'⟩
    · rw [hashSpec_toSpec, mem_boundarySet]
      intro hb
      exact hp _ hb (Std.ExtTreeMap.mem_iff_isSome_getElem?.mpr (by simp [hsr]))
    · intro hd
      obtain ⟨x, hx, he⟩ := (mem_digests hashSpec).mp hd
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hx)
      rw [hashSpec_toSpec, hashSpec_toSpec] at he
      have hsy := hstored y (List.mem_cons_of_mem _ hy)
      rw [he, hsr] at hsy
      cases hsy
      exact hin (List.mem_toFinset.mpr (List.mem_map_of_mem hy))

end BuiltRel

/-! ## The relative store -/

namespace RelStore

/-- A relative store has no collision. -/
theorem no_collision_model (c : RelStore) : ¬ CollisionIn hashSpec c.raw.abs :=
  c.built.no_collision

/-- A relative store's head cache is the spec's `headsRel`, as finite sets. -/
theorem heads_toFinset (c : RelStore) :
    c.heads.toList.toFinset = headsRel hashSpec c.raw.abs (boundarySet c.boundary) := by
  ext d
  rw [List.mem_toFinset, Std.ExtTreeSet.mem_toList]
  exact c.built.mem_heads_iff

/-- **Fetched relative to the boundary.** Everything reachable from the heads is a stored digest
or a boundary digest. If the store has no cycle, every stored record is reachable from the
heads. -/
theorem fetched_model (c : RelStore) :
    (∀ d, Reach hashSpec c.raw.abs (headsRel hashSpec c.raw.abs (boundarySet c.boundary)) d →
      d ∈ inView hashSpec c.raw.abs (boundarySet c.boundary)) ∧
    (Acyclic hashSpec c.raw.abs →
      Tight hashSpec c.raw.abs (headsRel hashSpec c.raw.abs (boundarySet c.boundary))) :=
  ⟨fun _ h => reach_mem_inView hashSpec c.built.closedRel h,
    fun hac => tight_of_acyclic hashSpec _ hac⟩

/-- **Same heads, same records, relative to the boundaries.** Two relative stores with the same
heads, neither with a cycle, and neither holding a record whose digest the other has only as a
boundary digest, hold the same records. Or two records collide. -/
theorem agree_model (c d : RelStore) (h : c.heads = d.heads)
    (hc : Acyclic hashSpec c.raw.abs) (hd : Acyclic hashSpec d.raw.abs)
    (hcd : ∀ r ∈ c.raw.abs, hashSpec r ∈ boundarySet d.boundary →
      hashSpec r ∈ digests hashSpec d.raw.abs)
    (hdc : ∀ r ∈ d.raw.abs, hashSpec r ∈ boundarySet c.boundary →
      hashSpec r ∈ digests hashSpec c.raw.abs) :
    c.raw.abs = d.raw.abs ∨ CollisionIn hashSpec (c.raw.abs ∪ d.raw.abs) := by
  have hh : headsRel hashSpec c.raw.abs (boundarySet c.boundary) =
      headsRel hashSpec d.raw.abs (boundarySet d.boundary) := by
    rw [← c.heads_toFinset, ← d.heads_toFinset, h]
  rcases newcomer_agree' hashSpec d.built.closedRel hh hcd (tight_of_acyclic hashSpec _ hc)
    with h1 | h1
  · rcases newcomer_agree' hashSpec c.built.closedRel hh.symm hdc (tight_of_acyclic hashSpec _ hd)
      with h2 | h2
    · exact .inl (h1.antisymm h2)
    · exact .inr h2
  · rw [Finset.union_comm] at h1
    exact .inr h1

/-! ### Accept -/

/-- In the `accepted` case, every link of the record is stored or a boundary digest. -/
theorem rawAcceptRel_accepted_links {c c' : RawStore} {B : Boundary} (hc : BuiltRel c B)
    {r : Rec} {d : Digest} (h : rawAcceptRel c B r = (.accepted d, c')) :
    ∀ l ∈ r.links, l ∈ c.map ∨ l ∈ B := by
  unfold rawAcceptRel at h
  dsimp only at h
  split at h
  · simp at h
  split at h
  · simp at h
  split at h
  · rename_i old hold
    split at h
    · rename_i hor
      subst hor
      exact hc.closed _ old hold
    · simp at h
  · split at h
    · simp at h
    · split at h
      · rename_i hempty
        intro l hl
        by_contra hn
        rw [not_or] at hn
        have : l ∈ missingLinksRel c.map B r := mem_missingLinksRel.mpr ⟨hl, hn.1, hn.2⟩
        simp_all
      · simp at h

/-- Collision: the record's digest holds another record. -/
theorem rawAcceptRel_collision {c c' : RawStore} {B : Boundary} {r : Rec} {d : Digest}
    (h : rawAcceptRel c B r = (.collision d, c')) :
    c' = c ∧ d = hashRecord r ∧ ∃ old, c.map[d]? = some old ∧ old ≠ r := by
  have hc : c' = c := by
    have := rawAcceptRel_unchanged (c := c) (B := B) (r := r) (by simp [h])
    rwa [h] at this
  unfold rawAcceptRel at h
  dsimp only at h
  split at h
  · simp at h
  split at h
  · simp at h
  split at h
  · rename_i old hold
    split at h
    · simp at h
    · rename_i hne
      obtain ⟨⟨⟩, rfl⟩ := Prod.mk.inj h
      exact ⟨rfl, rfl, old, hold, hne⟩
  · split at h
    · simp at h
    split at h <;> simp at h

/-- Wrong chat: the record's chat is not the store's. -/
theorem rawAcceptRel_wrongChat {c c' : RawStore} {B : Boundary} {r : Rec}
    (h : rawAcceptRel c B r = (.wrongChat, c')) : c' = c ∧ r.group ≠ c.group := by
  have hc : c' = c := by
    have := rawAcceptRel_unchanged (c := c) (B := B) (r := r) (by simp [h])
    rwa [h] at this
  unfold rawAcceptRel at h
  dsimp only at h
  split at h
  · rename_i hg
    exact ⟨hc, hg⟩
  split at h
  · simp at h
  split at h
  · split at h <;> simp at h
  · split at h
    · simp at h
    split at h <;> simp at h

/-- Too large: the record has too many links, or it is new and the store is full. -/
theorem rawAcceptRel_tooLarge {c c' : RawStore} {B : Boundary} {r : Rec}
    (h : rawAcceptRel c B r = (.tooLarge, c')) :
    c' = c ∧ (¬ r.WellSized ∨ (hashRecord r ∉ c.map ∧ maxRecords ≤ c.map.size + 1)) := by
  have hc : c' = c := by
    have := rawAcceptRel_unchanged (c := c) (B := B) (r := r) (by simp [h])
    rwa [h] at this
  unfold rawAcceptRel at h
  dsimp only at h
  split at h
  · simp at h
  split at h
  · rename_i hw
    exact ⟨hc, Or.inl hw⟩
  split at h
  · split at h <;> simp at h
  · rename_i hnone
    split at h
    · rename_i hfull
      refine ⟨hc, Or.inr ⟨?_, hfull⟩⟩
      simp [Std.ExtTreeMap.mem_iff_isSome_getElem?, hnone]
    split at h <;> simp at h

/-- Every result of `accept` means what `AcceptRelMeans` says. -/
theorem accept_means (c : RelStore) (r : Rec) : AcceptRelMeans c r (c.accept r) := by
  rcases h : c.accept r with ⟨res, c'⟩
  have hraw : rawAcceptRel c.raw c.boundary r = (res, c'.raw) := by
    have e : rawAcceptRel c.raw c.boundary r = ((c.accept r).1, (c.accept r).2.raw) := rfl
    rw [e, h]
  have hb : c'.boundary = c.boundary := by
    have e : (c.accept r).2.boundary = c.boundary := rfl
    rw [h] at e
    exact e
  have hext : c'.raw = c.raw → c' = c := fun he => ext he hb
  cases res with
  | accepted d =>
    obtain ⟨hd, _, hmap, hold⟩ := rawAcceptRel_accepted hraw
    have hlinks := rawAcceptRel_accepted_links c.built hraw
    have hsub : (toSpec r).links ⊆ inView hashSpec c.raw.abs (boundarySet c.boundary) := by
      intro l hl
      exact c.built.mem_inView.mpr (hlinks l (mem_toSpec_links.mp hl))
    have habs : c'.raw.abs = insert (toSpec r) c.raw.abs := RawStore.abs_insert hmap hold
    refine ⟨?_, hd, hsub, ?_, hb⟩
    · rw [acceptRel_of_resolves hashSpec hsub, habs]
    · rw [habs]; exact Finset.mem_insert_self _ _
  | missing ds =>
    obtain ⟨hc, hne, hmem, -⟩ := rawAcceptRel_missing hraw
    refine ⟨hext hc, hne, fun x => ?_⟩
    rw [hmem, mem_toSpec_links, c.built.mem_inView, not_or]
  | collision d =>
    obtain ⟨hc, hd, old, hold, hne⟩ := rawAcceptRel_collision hraw
    refine ⟨hext hc, hd, toSpec old, RawStore.mem_abs.mpr ⟨d, old, hold, rfl⟩, ?_, ?_⟩
    · rw [hashSpec_toSpec]; exact c.built.hash_eq d old hold
    · exact fun he => hne (toSpec_injective he)
  | wrongChat =>
    obtain ⟨hc, hg⟩ := rawAcceptRel_wrongChat hraw
    exact ⟨hext hc, hg⟩
  | tooLarge =>
    obtain ⟨hc, hw⟩ := rawAcceptRel_tooLarge hraw
    refine ⟨hext hc, ?_⟩
    rcases hw with hw | ⟨hn, hs⟩
    · exact Or.inl hw
    · exact Or.inr ⟨by rwa [c.built.mem_digests_abs], hs⟩

/-! ### Equal records, equal stores -/

/-- **Two relative stores of one chat, with the same boundary and the same records, are equal.**
The map is fixed by the records, and the heads by the map and the boundary. -/
theorem eq_of_abs {c d : RelStore} (hg : c.group = d.group) (hb : c.boundary = d.boundary)
    (h : c.raw.abs = d.raw.abs) : c = d := by
  have hmap : c.raw.map = d.raw.map := by
    apply Std.ExtTreeMap.ext_getElem?
    intro k
    apply Option.ext
    intro r
    rw [c.built.getElem?_eq_some_iff, d.built.getElem?_eq_some_iff, h]
  have hheads : c.raw.heads = d.raw.heads := by
    apply Std.ExtTreeSet.ext_mem
    intro x
    rw [c.built.heads_iff, d.built.heads_iff, hmap, hb]
  apply ext _ hb
  have hg' : c.raw.group = d.raw.group := hg
  cases hc : c.raw
  cases hd : d.raw
  rw [hc, hd] at hg' hmap hheads
  simp only at hg' hmap hheads
  rw [hg', hmap, hheads]

/-! ### Merge -/

/-- What `addBoundaryAll` does to the boundary: it keeps every digest, adds only listed ones, and
every listed digest ends up stored or in the boundary. The records do not change. -/
theorem addBoundaryAll_mem {c e : RelStore} {es : List (Digest × Aci)}
    (h : c.addBoundaryAll es = some e) :
    e.raw.map = c.raw.map ∧ (∀ x, x ∈ c.boundary → x ∈ e.boundary) ∧
      (∀ x, x ∈ e.boundary → x ∈ c.boundary ∨ ∃ a, (x, a) ∈ es) ∧
      (∀ x a, (x, a) ∈ es → x ∈ e.raw.map ∨ x ∈ e.boundary) := by
  induction es generalizing c with
  | nil =>
    simp only [addBoundaryAll, Option.some.injEq] at h
    subst h
    exact ⟨rfl, fun _ h => h, fun _ h => .inl h, by simp⟩
  | cons p rest ih =>
    obtain ⟨d, v⟩ := p
    simp only [addBoundaryAll, Option.bind_eq_some_iff] at h
    obtain ⟨c', h1, h2⟩ := h
    obtain ⟨-, hm, hdin, hkeep, hnew⟩ := addBoundary_spec h1
    obtain ⟨hm', hkeep', hsub', hall'⟩ := ih h2
    have mem_of : ∀ (t : Boundary) x, x ∈ t ↔ ∃ a, t[x]? = some a := fun t x =>
      Std.ExtTreeMap.mem_iff_isSome_getElem?.trans Option.isSome_iff_exists
    refine ⟨hm'.trans hm, fun x hx => hkeep' x ?_, fun x hx => ?_, fun x a hx => ?_⟩
    · obtain ⟨a, ha⟩ := (mem_of _ x).mp hx
      exact (mem_of _ x).mpr ⟨a, hkeep x a ha⟩
    · rcases hsub' x hx with hx' | ⟨a, ha⟩
      · obtain ⟨a, ha⟩ := (mem_of _ x).mp hx'
        rcases hnew x a ha with ha' | ⟨rfl, rfl⟩
        · exact .inl ((mem_of _ x).mpr ⟨a, ha'⟩)
        · exact .inr ⟨a, List.mem_cons_self⟩
      · exact .inr ⟨a, List.mem_cons_of_mem _ ha⟩
    · rcases List.mem_cons.mp hx with he | hx
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
        rcases hdin with hd | hd
        · exact .inl (hm' ▸ hd)
        · obtain ⟨a', ha'⟩ := (mem_of _ _).mp hd
          exact .inr (hkeep' _ ((mem_of _ _).mpr ⟨a', ha'⟩))
      · exact hall' x a hx

/-- **A merged store holds the records of both stores, and knows the digests both know.** -/
theorem merge_model {c d e : RelStore} (h : c.merge d = .ok e) :
    e.raw.abs = c.raw.abs ∪ d.raw.abs ∧
      inView hashSpec e.raw.abs (boundarySet e.boundary) =
        inView hashSpec c.raw.abs (boundarySet c.boundary) ∪
          inView hashSpec d.raw.abs (boundarySet d.boundary) := by
  obtain ⟨-, -, hmap⟩ := merge_ok h
  have hmem : ∀ x, x ∈ e.raw.map ↔ x ∈ c.raw.map ∨ x ∈ d.raw.map := by
    intro x
    simp only [Std.ExtTreeMap.mem_iff_isSome_getElem?, Option.isSome_iff_exists, hmap]
    constructor
    · rintro ⟨r, hr | hr⟩
      · exact .inl ⟨r, hr⟩
      · exact .inr ⟨r, hr⟩
    · rintro (⟨r, hr⟩ | ⟨r, hr⟩)
      · exact ⟨r, .inl hr⟩
      · exact ⟨r, .inr hr⟩
  have habs : e.raw.abs = c.raw.abs ∪ d.raw.abs := by
    ext x
    simp only [Finset.mem_union, RawStore.mem_abs, hmap]
    constructor
    · rintro ⟨k, r, hr | hr, rfl⟩
      · exact .inl ⟨k, r, hr, rfl⟩
      · exact .inr ⟨k, r, hr, rfl⟩
    · rintro (⟨k, r, hr, rfl⟩ | ⟨k, r, hr, rfl⟩)
      · exact ⟨k, r, .inl hr, rfl⟩
      · exact ⟨k, r, .inr hr, rfl⟩
  refine ⟨habs, ?_⟩
  -- The boundary of `e` is the boundary `addBoundaryAll` made.
  unfold merge at h
  split at h
  · simp at h
  split at h
  · simp at h
  rename_i c' hadd
  obtain ⟨hm0, hkeep, hsub, hall⟩ := addBoundaryAll_mem hadd
  obtain ⟨-, hb, -⟩ := acceptAll_sound c' d.records
  generalize c'.acceptAll d.records = res at h hb
  obtain ⟨e', left⟩ := res
  dsimp only at h hb
  split at h
  · simp only [Except.ok.injEq] at h
    subst h
    have hdb : ∀ x, x ∈ d.boundary ↔ ∃ a, (x, a) ∈ d.boundary.toList := fun x =>
      (Std.ExtTreeMap.mem_iff_isSome_getElem?.trans Option.isSome_iff_exists).trans
        (exists_congr fun _ => Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some.symm)
    ext x
    rw [Finset.mem_union, e'.built.mem_inView, c.built.mem_inView, d.built.mem_inView, hmem, hb]
    constructor
    · rintro ((hx | hx) | hx)
      · exact .inl (.inl hx)
      · exact .inr (.inl hx)
      · rcases hsub x hx with hx | hx
        · exact .inl (.inr hx)
        · exact .inr (.inr ((hdb x).mpr hx))
    · rintro ((hx | hx) | (hx | hx))
      · exact .inl (.inl hx)
      · exact .inr (hkeep x hx)
      · exact .inl (.inr hx)
      · obtain ⟨a, ha⟩ := (hdb x).mp hx
        rcases hall x a ha with hx | hx
        · exact .inl (.inl (hm0 ▸ hx))
        · exact .inr hx
  · simp at h

/-! ### Load -/

/-- **`acceptAll` on an empty store over `B` takes in its batch**: when the records are within the
size limits, all of the chat, and no two different records share a digest, every record of the
batch whose links are all stored or boundary digests is stored. -/
theorem acceptAll_takesIn {g : GroupId} {B : Boundary} (hB : B.size < maxRecords) {u : Array Rec}
    (hw : WellSized u) (hg : ∀ r ∈ u, r.group = g) (hcol : NoCollision u) :
    ∀ x ∈ u, (∀ d ∈ x.links, d ∈ ((emptyWith g B hB).acceptAll u).1.raw.map ∨ d ∈ B) →
      ((emptyWith g B hB).acceptAll u).1.raw.map[hashRecord x]? = some x := by
  obtain ⟨hgrp, hbnd, _, honly, hstored, -⟩ := acceptAll_sound (emptyWith g B hB) u
  have hstuck := acceptAll_stuck (emptyWith g B hB) u
  generalize (emptyWith g B hB).acceptAll u = res at hgrp hbnd honly hstored hstuck ⊢
  obtain ⟨e, left⟩ := res
  dsimp only at hgrp hbnd honly hstored hstuck ⊢
  have honly' : ∀ k x, e.raw.map[k]? = some x → x ∈ u := fun k x hk =>
    (honly k x hk).resolve_left (by simp [emptyWith])
  have hegrp : e.raw.group = g := hgrp
  have hebnd : e.boundary = B := hbnd
  intro x hx hl
  have hok : (rawAcceptRel e.raw e.boundary x).1 = .accepted (hashRecord x) := by
    apply rawAcceptRel_of_ok ((hg x hx).trans hegrp.symm) (hw.2 x hx) (hebnd ▸ hl)
    · intro old hold
      exact hcol old (honly' _ _ hold) x hx (e.built.hash_eq _ _ hold)
    · intro hn
      have := CheckedStore.size_lt_of_keys (m := e.raw.map) (u := u) (r := x) (fun k hk => by
        obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp
          (Std.ExtTreeMap.mem_iff_isSome_getElem?.mp hk)
        exact ⟨y, honly' k y hy, e.built.hash_eq k y hy⟩) hx hn
      have := hw.1
      omega
  by_cases hxl : x ∈ left
  · exact absurd (by rw [accept_fst]; exact hok) (hstuck x hxl (hashRecord x))
  · exact hstored x hx hxl

/-- `load` succeeds on records within the size limits, all of chat `g`, with no collision, that
are accept-built relative to `B` in the spec model. -/
theorem load_ok_of_model {g : GroupId} {B : Boundary} {u : Array Rec} (hB : B.size < maxRecords)
    (hw : WellSized u) (hg : ∀ r ∈ u, r.group = g) (hcol : NoCollision u)
    (hab : AcceptBuiltRel hashSpec (boundarySet B) (specOf u)) : ∃ c, load g B u = .ok c := by
  have hchat : CheckedStore.allInChat g u = true := by
    simp only [CheckedStore.allInChat, Array.all_eq_true_iff_forall_mem, beq_iff_eq]
    exact hg
  have hcheck : CheckedStore.checkInput g u = none := by
    simp [CheckedStore.checkInput, hw, hchat]
  have htake := acceptAll_takesIn hB hw hg hcol
  unfold load
  simp only [hB, ↓reduceDIte, hcheck]
  obtain ⟨-, hbnd, -, -, -, hleftsub⟩ := acceptAll_sound (emptyWith g B hB) u
  have hstuck := acceptAll_stuck (emptyWith g B hB) u
  generalize (emptyWith g B hB).acceptAll u = res at hbnd hleftsub hstuck htake ⊢
  obtain ⟨e, left⟩ := res
  dsimp only at hbnd hleftsub hstuck htake ⊢
  have hebnd : e.boundary = B := hbnd
  -- Every record of `u` is stored: `e` takes in `specOf u`, which is accept-built.
  have hsub : specOf u ⊆ e.raw.abs := by
    apply subset_of_takesInRel hashSpec hab
    intro R hR hl
    obtain ⟨x, hx, rfl⟩ := mem_specOf.mp hR
    refine RawStore.mem_abs.mpr ⟨_, x, htake x hx fun d hd => ?_, rfl⟩
    have := hl (mem_toSpec_links.mpr hd)
    rw [← hebnd]
    exact e.built.mem_inView.mp (hebnd ▸ this)
  have hall : ∀ x ∈ u, e.raw.map[hashRecord x]? = some x := fun x hx =>
    (e.built.getElem?_eq_some_iff).mpr ⟨hsub (toSpec_mem_specOf.mpr hx), rfl⟩
  have hleft : left = #[] := by
    rw [Array.eq_empty_iff_forall_not_mem]
    intro x hx
    have hs := hall x (hleftsub x hx)
    exact hstuck x hx (hashRecord x) (by
      rw [accept_fst]
      exact rawAcceptRel_of_ok (e.built.group_eq _ x hs) (e.built.wellSized _ x hs)
        (e.built.closed _ x hs) (fun old ho => by rw [hs] at ho; exact (Option.some.inj ho).symm)
        (fun hn => absurd (Std.ExtTreeMap.mem_iff_isSome_getElem?.mpr (by simp [hs])) hn))
  simp [hleft]

/-- **`load`, in the spec model** (`OPEN` of a relative blob runs `load` over the blob's
boundary, `ChatStore.openStore`). `load g B u` gives the store `c` exactly when the boundary is
under its limit, the records `u` are within the size limits, accept-built relative to `B`, free of
collisions and all of chat `g`; and `c` is the store of chat `g` over the boundary `B` holding
exactly the records of `u`. -/
theorem load_iff_model {g : GroupId} {B : Boundary} {u : Array Rec} {c : RelStore} :
    load g B u = .ok c ↔
      B.size < maxRecords ∧ WellSized u ∧ AcceptBuiltRel hashSpec (boundarySet B) (specOf u) ∧
        ¬ CollisionIn hashSpec (specOf u) ∧ (∀ r ∈ u, r.group = g) ∧ c.raw.abs = specOf u ∧
        c.group = g ∧ c.boundary = B := by
  constructor
  · intro h
    obtain ⟨hcg, hcb, hw, hg, hmap⟩ := load_ok h
    have habs : c.raw.abs = specOf u := by
      ext x
      rw [RawStore.mem_abs, mem_specOf]
      constructor
      · rintro ⟨k, r, hk, rfl⟩
        exact ⟨r, ((hmap k r).mp hk).1, rfl⟩
      · rintro ⟨r, hr, rfl⟩
        exact ⟨_, r, (hmap _ r).mpr ⟨hr, rfl⟩, rfl⟩
    refine ⟨hcb ▸ c.built.boundary_lt, hw, ?_, habs ▸ c.built.no_collision, hg, habs, hcg, hcb⟩
    rw [← habs, ← hcb]
    exact c.built.acceptBuiltRel
  · rintro ⟨hB, hw, hab, hncol, hg, habs, hcg, hcb⟩
    obtain ⟨e, he⟩ := load_ok_of_model hB hw hg (CheckedStore.noCollision_of_specOf hncol) hab
    rw [he]
    obtain ⟨heg, heb, -, -, hemap⟩ := load_ok he
    have heabs : e.raw.abs = specOf u := by
      ext x
      rw [RawStore.mem_abs, mem_specOf]
      constructor
      · rintro ⟨k, r, hk, rfl⟩
        exact ⟨r, ((hemap k r).mp hk).1, rfl⟩
      · rintro ⟨r, hr, rfl⟩
        exact ⟨_, r, (hemap _ r).mpr ⟨hr, rfl⟩, rfl⟩
    exact congrArg Except.ok (eq_of_abs (heg.trans hcg.symm) (heb.trans hcb.symm)
      (heabs.trans habs.symm))

/-- **A relative store reloads as itself** (`load_reopens`, the relative `encode_open`). -/
theorem load_records (c : RelStore) : load c.group c.boundary c.records = .ok c :=
  load_reopens c

/-! ### Salvage -/

/-- What `findCollision` looks up for a digest: the stored record, or else the one seen so far. -/
def lookup (c : RelStore) (seen : RecMap) (d : Digest) : Option Rec :=
  (c.get d).orElse fun _ => seen[d]?

example : lookup (empty Examples.group) ∅ (hashRecord Examples.a1) = none := by
  simp [lookup, get, empty, emptyWith]

/-- Adding a record at a digest where the lookup found nothing changes no other lookup that
found something. -/
theorem lookup_insert {c : RelStore} {seen : RecMap} {d d' : Digest} {y z : Rec}
    (hnone : lookup c seen d' = none) (h : lookup c seen d = some z) :
    lookup c (seen.insert d' y) d = some z := by
  unfold lookup at *
  cases hg : c.get d with
  | some w => simp_all [Option.orElse]
  | none =>
    simp only [hg, Option.orElse] at h ⊢
    rw [Std.ExtTreeMap.getElem?_insert]
    split
    · rename_i hk
      rw [Std.LawfulEqCmp.compare_eq_iff_eq] at hk
      subst hk
      cases hg' : c.get d' with
      | some w => rw [hg] at hg'; cases hg'
      | none => simp [hg', Option.orElse, h] at hnone
    · exact h

/-- The fold inside `findCollision`, given by what each step does (as for a closed store). -/
theorem fold_lookup {c : RelStore} {F : RecMap × DigestSet → Rec → RecMap × DigestSet}
    (h1 : ∀ seen found y, lookup c seen (hashRecord y) = some y → F (seen, found) y = (seen, found))
    (h2 : ∀ seen found y z, lookup c seen (hashRecord y) = some z → z ≠ y →
      F (seen, found) y = (seen, found.insert (hashRecord y)))
    (h3 : ∀ seen found y, lookup c seen (hashRecord y) = none →
      F (seen, found) y = (seen.insert (hashRecord y) y, found)) :
    ∀ (l : List Rec) (seen : RecMap) (found : DigestSet), (l.foldl F (seen, found)).2 = ∅ →
      found = ∅ ∧
        (∀ d z, lookup c seen d = some z → lookup c (l.foldl F (seen, found)).1 d = some z) ∧
        ∀ y ∈ l, lookup c (l.foldl F (seen, found)).1 (hashRecord y) = some y := by
  intro l
  induction l with
  | nil => intro seen found h; exact ⟨h, fun _ _ h => h, by simp⟩
  | cons y ys ih =>
    intro seen found h
    simp only [List.foldl_cons] at h ⊢
    cases hl : lookup c seen (hashRecord y) with
    | some z =>
      by_cases hz : z = y
      · subst hz
        rw [h1 _ _ _ hl] at h ⊢
        obtain ⟨hf, hst, hall⟩ := ih seen found h
        refine ⟨hf, hst, ?_⟩
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hst _ _ hl
        · exact hall x hx
      · rw [h2 _ _ _ _ hl hz] at h
        exact absurd (ih seen _ h).1 Std.ExtTreeSet.insert_ne_empty
    | none =>
      rw [h3 _ _ _ hl] at h ⊢
      obtain ⟨hf, hst, hall⟩ := ih _ found h
      have hy : lookup c (seen.insert (hashRecord y) y) (hashRecord y) = some y := by
        unfold lookup at hl ⊢
        cases hg : c.get (hashRecord y) with
        | some w => simp [hg, Option.orElse] at hl
        | none => simp [Option.orElse]
      refine ⟨hf, fun d z hd => hst d z (lookup_insert hl hd), ?_⟩
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hst _ _ hy
      · exact hall x hx

/-- **`findCollision` is right:** when it finds nothing, no record left over shares its digest
with a different record left over or stored. -/
theorem noCollision_of_findCollision {c : RelStore} {left : Array Rec}
    (h : c.findCollision (CheckedStore.withDigests left) = none) :
    ∀ x ∈ left, ∀ y, (y ∈ left ∨ c.raw.map[hashRecord y]? = some y) →
      hashRecord x = hashRecord y → x = y := by
  simp only [findCollision, CheckedStore.withDigests, ← Array.foldl_toList, Array.toList_map,
    List.foldl_map, Std.ExtTreeSet.min?_eq_none_iff] at h
  obtain ⟨-, -, hall⟩ := fold_lookup (c := c)
    (fun seen found y hl => by simp only [lookup] at hl; dsimp only; rw [hl]; simp)
    (fun seen found y z hl hz => by simp only [lookup] at hl; dsimp only; rw [hl]; simp [hz])
    (fun seen found y hl => by simp only [lookup] at hl; dsimp only; rw [hl])
    left.toList ∅ ∅ h
  intro x hx y hy hxy
  have hlx := hall x (Array.mem_toList_iff.mpr hx)
  rcases hy with hy | hy
  · have hly := hall y (Array.mem_toList_iff.mpr hy)
    rw [hxy, hly] at hlx
    exact (Option.some.inj hlx).symm
  · have hs : c.get (hashRecord y) = some y := hy
    unfold lookup at hlx
    rw [hxy, hs] at hlx
    exact (Option.some.inj hlx).symm

/-- `findCollision` finds nothing when no record left over shares its digest with a different
record left over or stored. -/
theorem findCollision_eq_none {c : RelStore} {left : Array Rec}
    (hcol : ∀ x ∈ left, ∀ y, (y ∈ left ∨ c.raw.map[hashRecord y]? = some y) →
      hashRecord x = hashRecord y → x = y) :
    c.findCollision (CheckedStore.withDigests left) = none := by
  simp only [findCollision, CheckedStore.withDigests, ← Array.foldl_toList, Array.toList_map,
    List.foldl_map]
  have h0 : ∀ d o, (∅ : RecMap)[d]? = some o → o ∈ left ∧ hashRecord o = d := by simp
  have hl : ∀ x ∈ left.toList, x ∈ left := fun x hx => Array.mem_toList_iff.mp hx
  generalize (∅ : RecMap) = seen at h0 ⊢
  generalize left.toList = l at hl ⊢
  suffices h : (List.foldl _ (seen, (∅ : DigestSet)) l).snd = ∅ by rw [h]; simp
  induction l generalizing seen with
  | nil => rfl
  | cons r rs ih =>
    simp only [List.foldl_cons]
    have hr : r ∈ left := hl r List.mem_cons_self
    have hrs : ∀ x ∈ rs, x ∈ left := fun x hx => hl x (List.mem_cons_of_mem _ hx)
    cases hg : c.get (hashRecord r) with
    | some other =>
      have hg' : c.raw.map[hashRecord r]? = some other := hg
      have : other = r := by
        have hh := c.built.hash_eq _ _ hg'
        have hs : c.raw.map[hashRecord other]? = some other := by rw [hh]; exact hg'
        exact (hcol r hr other (.inr hs) hh.symm).symm
      simp only [Option.orElse, this, ↓reduceIte]
      exact ih seen h0 hrs
    | none =>
      cases hs : seen[hashRecord r]? with
      | some other =>
        obtain ⟨ho, hh⟩ := h0 _ _ hs
        have : other = r := (hcol r hr other (Or.inl ho) hh.symm).symm
        simp only [Option.orElse, this, ↓reduceIte]
        exact ih seen h0 hrs
      | none =>
        simp only [Option.orElse]
        refine ih _ ?_ hrs
        intro d o hd
        rw [Std.ExtTreeMap.getElem?_insert] at hd
        split at hd
        · rename_i hk
          rw [Std.LawfulEqCmp.compare_eq_iff_eq] at hk
          cases hd
          exact ⟨hr, hk⟩
        · exact h0 d o hd

/-- **When salvage succeeds.** `salvage g B u` loads something whenever the boundary is under its
limit, the records are within the size limits, all of chat `g`, and no two different records
share a digest. -/
theorem salvage_ok_of {g : GroupId} {B : Boundary} {u : Array Rec} (hB : B.size < maxRecords)
    (hw : WellSized u) (hg : ∀ r ∈ u, r.group = g) (hcol : NoCollision u) :
    ∃ s, salvage g B u = .ok s := by
  have hchat : CheckedStore.allInChat g u = true := by
    simp only [CheckedStore.allInChat, Array.all_eq_true_iff_forall_mem, beq_iff_eq]
    exact hg
  have hcheck : CheckedStore.checkInput g u = none := by
    simp [CheckedStore.checkInput, hw, hchat]
  obtain ⟨-, -, -, honly, -, hleftsub⟩ := acceptAll_sound (emptyWith g B hB) u
  unfold salvage
  simp only [hB, ↓reduceDIte, hcheck]
  generalize (emptyWith g B hB).acceptAll u = res at honly hleftsub ⊢
  obtain ⟨e, left⟩ := res
  dsimp only at honly hleftsub ⊢
  have honly' : ∀ k x, e.raw.map[k]? = some x → x ∈ u := fun k x hk =>
    (honly k x hk).resolve_left (by simp [emptyWith])
  rw [findCollision_eq_none (fun x hx y hy hxy =>
    hcol x (hleftsub x hx) y (hy.elim (hleftsub y) (honly' _ y)) hxy)]
  exact ⟨_, rfl⟩

/-- The digests the fold in `leftoverReport` collects: those of the given entries. -/
theorem mem_leftoverReport_fst {c : RelStore} {left : Array (Digest × Rec)} {d : Digest} :
    d ∈ (c.leftoverReport left).1 ↔ ∃ p ∈ left, p.1 = d := by
  simp only [leftoverReport, List.mem_toArray, Std.ExtTreeSet.mem_toList]
  rw [← Array.foldl_toList]
  rw [CheckedStore.mem_fold_insert]
  simp

/-- The `dropped` list of `leftoverReport` is sorted, with no digest twice. -/
theorem leftoverReport_fst_sorted {c : RelStore} {left : Array (Digest × Rec)} :
    StrictlySorted (c.leftoverReport left).1 := by
  unfold StrictlySorted leftoverReport
  exact Std.ExtTreeSet.ordered_toList

/-- **`salvage`, in the spec model.** If `salvage g B u` loads `s`, then the records `u` have no
collision, the store holds exactly what the model's salvage relative to `B` keeps
(`buildRetryRel`: accept what can be accepted, in any order, until nothing more can), it is of
chat `g` over the boundary `B`, and `dropped` is sorted and holds exactly the digests of the other
records of `u`. -/
theorem salvage_model {g : GroupId} {B : Boundary} {u : Array Rec} {s : Salvaged}
    (h : salvage g B u = .ok s) :
    ¬ CollisionIn hashSpec (specOf u) ∧
      s.store.raw.abs = buildRetryRel hashSpec (boundarySet B) (specOf u) ∧ s.store.group = g ∧
      s.store.boundary = B ∧
      (∀ d, d ∈ s.dropped ↔
        d ∈ digests hashSpec (specOf u \ buildRetryRel hashSpec (boundarySet B) (specOf u))) ∧
      StrictlySorted s.dropped := by
  unfold salvage at h
  split at h
  swap
  · simp at h
  rename_i hB
  split at h
  · simp at h
  rename_i hcheck
  obtain ⟨hw, hchat⟩ := CheckedStore.checkInput_eq_none_iff.mp hcheck
  obtain ⟨hgrp, hbnd, _, honly, hstored, hleftsub⟩ := acceptAll_sound (emptyWith g B hB) u
  have htake := acceptAll_takesIn hB hw hchat
  have hstuck := acceptAll_stuck (emptyWith g B hB) u
  generalize (emptyWith g B hB).acceptAll u = res at h hgrp hbnd honly hstored hleftsub htake hstuck
  obtain ⟨e, left⟩ := res
  dsimp only at h hgrp hbnd honly hstored hleftsub htake hstuck
  split at h
  · simp at h
  rename_i hf
  simp only [Except.ok.injEq] at h
  subst h
  have honly' : ∀ k x, e.raw.map[k]? = some x → x ∈ u := fun k x hk =>
    (honly k x hk).resolve_left (by simp [emptyWith])
  -- No collision among `u`: a record of `u` is left over or stored.
  have hcol0 := noCollision_of_findCollision hf
  have hor : ∀ y ∈ u, y ∈ left ∨ e.raw.map[hashRecord y]? = some y := fun y hy =>
    if hl : y ∈ left then .inl hl else .inr (hstored y hy hl)
  have hcol : NoCollision u := by
    intro x hx y hy hxy
    rcases hor x hx with hxl | hxs
    · exact hcol0 x hxl y (hor y hy) hxy
    · rcases hor y hy with hyl | hys
      · exact (hcol0 y hyl x (.inr hxs) hxy.symm).symm
      · rw [hxy, hys] at hxs
        exact (Option.some.inj hxs).symm
  have hebnd : e.boundary = B := hbnd
  -- The store is exactly the model's salvage.
  have habs : e.raw.abs = buildRetryRel hashSpec (boundarySet B) (specOf u) := by
    symm
    apply buildRetryRel_eq_of_takesIn hashSpec
    · intro x hx
      obtain ⟨r, rfl, hr⟩ := e.built.exists_of_mem_abs hx
      exact toSpec_mem_specOf.mpr (honly' _ r hr)
    · rw [← hebnd]; exact e.built.acceptBuiltRel
    · intro R hR hl
      obtain ⟨x, hx, rfl⟩ := mem_specOf.mp hR
      refine RawStore.mem_abs.mpr ⟨_, x, htake hcol x hx fun d hd => ?_, rfl⟩
      rw [← hebnd]
      exact e.built.mem_inView.mp (hebnd ▸ hl (mem_toSpec_links.mpr hd))
  -- A left-over record is not stored: `accept` would take it again.
  have hnotStored : ∀ x ∈ left, e.raw.map[hashRecord x]? ≠ some x := by
    intro x hx hs
    exact hstuck x hx (hashRecord x) (by
      rw [accept_fst]
      exact rawAcceptRel_of_ok (e.built.group_eq _ x hs) (e.built.wellSized _ x hs)
        (e.built.closed _ x hs) (fun old ho => by rw [hs] at ho; exact (Option.some.inj ho).symm)
        (fun hn => absurd (Std.ExtTreeMap.mem_iff_isSome_getElem?.mpr (by simp [hs])) hn))
  have hmemAbs : ∀ x, toSpec x ∈ e.raw.abs ↔ e.raw.map[hashRecord x]? = some x := fun x => by
    rw [e.built.getElem?_eq_some_iff]; simp
  refine ⟨CheckedStore.not_collisionIn_specOf hcol, habs, hgrp, hbnd, fun d => ?_,
    leftoverReport_fst_sorted (c := e)⟩
  dsimp only
  rw [mem_leftoverReport_fst, ← habs, mem_digests]
  simp only [CheckedStore.withDigests, Array.mem_map]
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨toSpec x, Finset.mem_sdiff.mpr ⟨toSpec_mem_specOf.mpr (hleftsub x hx),
      fun h => hnotStored x hx ((hmemAbs x).mp h)⟩, hashSpec_toSpec x⟩
  · rintro ⟨R, hR, rfl⟩
    obtain ⟨hRu, hRn⟩ := Finset.mem_sdiff.mp hR
    obtain ⟨x, hx, rfl⟩ := mem_specOf.mp hRu
    have hxl : x ∈ left := by
      by_contra hxl
      exact hRn ((hmemAbs x).mpr (hstored x hx hxl))
    exact ⟨_, ⟨x, hxl, rfl⟩, (hashSpec_toSpec x).symm⟩

/-! ### Confirmation -/

/-- `has` asks the spec store. -/
theorem has_iff (c : RelStore) {d : Digest} : c.has d = true ↔ d ∈ digests hashSpec c.raw.abs := by
  rw [has, Std.ExtTreeMap.contains_iff_mem, c.built.mem_digests_abs]

/-- **Confirmation, relative to the sender's boundary.** A live message links the digests `hs`,
and the sender's store `d` holds a record for each. Then each digest the links reach in your store
`c` is reached in the sender's store too; or your store reaches it from a digest `b` that the
sender holds only as a boundary digest (`boundaryDigests`), which the links reach in the sender's
store. Or two records, across the two stores, collide. With no boundary on either side, applying
this both ways gives `CheckedStore.confirmed`. -/
theorem confirmed_model (c d : RelStore) (hs : Array Digest) (hd : ∀ h ∈ hs, d.has h = true) :
    (∀ x, Reach hashSpec c.raw.abs hs.toList.toFinset x →
      Reach hashSpec d.raw.abs hs.toList.toFinset x ∨
        ∃ b ∈ d.boundaryDigests, Reach hashSpec d.raw.abs hs.toList.toFinset b ∧
          Reach hashSpec c.raw.abs {b} x) ∨
      CollisionIn hashSpec (c.raw.abs ∪ d.raw.abs) := by
  have hsT : hs.toList.toFinset ⊆ digests hashSpec d.raw.abs := fun x hx =>
    (d.has_iff).mp (hd x (Array.mem_toList_iff.mp (List.mem_toFinset.mp hx)))
  refine (reach_transfer hashSpec d.built.closedRel hsT).imp_left fun h x hx => ?_
  refine (h x hx).imp_right fun ⟨b, hb, hbn, hRb, hRS⟩ => ⟨b, ?_, hRb, hRS⟩
  rw [mem_boundaryDigests, ← mem_boundarySet, ← d.built.mem_digests_abs]
  exact ⟨hb, hbn⟩

end RelStore

end Zrdt
