/-
Copyright (c) 2026 zrdt contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: zrdt contributors
-/
import Mathlib
import Crdt.Merkle.Bridge

set_option linter.unusedSectionVars false

/-!
# Each store operation, seen in the spec model (docs/PLAN.md §3.2, phase B)

`Bridge.lean` maps a shipped store `c` to `abs c`, a finite set of spec records. This file says
what each operation of `Zrdt.CheckedStore` does to `abs c`, in the words of the spec
(`Crdt.Merkle`):

* `accept` (`abs_accept_accepted`, `abs_accept_missing`, `abs_accept_collision`,
  `abs_accept_wrongChat`, `abs_accept_tooLarge`): an accepted record is the spec's `accept`; any
  other result leaves the store as it was, and says why. The `missing` list is exactly the links
  the spec store does not hold.
* `merge` (`abs_merge`): a merged store holds the records of both stores.
* `heads` (`heads_eq`), `has` (`has_iff`), `get` (`get_eq_some_iff`): the observers read the spec
  store.
* `reachSet` (`reachSet_iff`): the walk finds exactly the digests of the spec's `reachSet`.
* `open` (`open_sound`, `open_complete`, `open_iff`), `salvage` (`salvage_spec`), `encode`
  (`encode_open`).
* `eq_of_abs`: two stores of one chat that hold the same records are equal.

The statements advertised to readers are restated in `Api.lean`.
-/

namespace Zrdt

open Crdt.Merkle

/-! ## Small facts -/

/-- Two digests compare equal exactly when they are equal. -/
theorem Digest.compare_eq_iff {a b : Digest} : compare a b = .eq ↔ a = b :=
  Std.LawfulEqCmp.compare_eq_iff_eq

/-- The spec records of a list of shipped records, as a finite set. `open` and `salvage` are
stated with it: `specOf u` is the spec store of the records `u` read from a blob. -/
def specOf (u : Array Rec) : SpecStore := (u.toList.map toSpec).toFinset

example : specOf #[] = ∅ := rfl

/-- A spec record is in `specOf u` exactly when it is the spec record of a record of `u`. -/
@[simp] theorem mem_specOf {u : Array Rec} {x : SpecRec} :
    x ∈ specOf u ↔ ∃ r ∈ u, toSpec r = x := by
  simp [specOf]

/-- `toSpec r` is in `specOf u` exactly when `r` is in `u`. -/
theorem toSpec_mem_specOf {u : Array Rec} {r : Rec} : toSpec r ∈ specOf u ↔ r ∈ u := by
  rw [mem_specOf]
  constructor
  · rintro ⟨r', hr', he⟩
    rwa [← toSpec_injective he]
  · intro h
    exact ⟨r, h, rfl⟩

/-- Turning a spec record into a shipped one and back gives the same spec record. -/
@[simp] theorem toSpec_ofSpec (x : SpecRec) : toSpec (ofSpec x) = x := by
  obtain ⟨⟨g, k⟩, ls, a⟩ := x
  simp only [toSpec, ofSpec, List.toList_toArray]
  congr 1
  · exact Finset.sort_toFinset ls _

/-- In a correct store, `toSpec r` is in the spec store exactly when `r` is stored under its own
digest. -/
theorem Built.toSpec_mem_abs {c : RawStore} (h : Built c) {r : Rec} :
    toSpec r ∈ c.abs ↔ c.map[hashRecord r]? = some r := by
  rw [RawStore.mem_abs]
  constructor
  · rintro ⟨k, r', hk, he⟩
    have := toSpec_injective he
    subst this
    rwa [h.hash_eq k r' hk]
  · intro hr
    exact ⟨_, r, hr, rfl⟩

/-- In a correct store, every spec record is the spec record of a record stored under its own
digest. -/
theorem Built.exists_of_mem_abs {c : RawStore} (h : Built c) {x : SpecRec} (hx : x ∈ c.abs) :
    ∃ r, toSpec r = x ∧ c.map[hashRecord r]? = some r := by
  obtain ⟨k, r, hk, rfl⟩ := RawStore.mem_abs.mp hx
  exact ⟨r, rfl, by rwa [h.hash_eq k r hk]⟩

/-- In a correct store, a digest is stored exactly when the spec store holds a record with that
hash. -/
theorem Built.mem_map_iff {c : RawStore} (h : Built c) {d : Digest} :
    d ∈ c.map ↔ d ∈ digests hashSpec c.abs :=
  h.mem_digests_abs.symm

/-- Inserting a record under its digest adds its spec record (if a record is already stored
under that digest, it must be the same record). -/
theorem RawStore.abs_insert {c c' : RawStore} {r : Rec} {d : Digest}
    (hmap : c'.map = c.map.insert d r) (hold : ∀ old, c.map[d]? = some old → old = r) :
    c'.abs = insert (toSpec r) c.abs := by
  ext x
  rw [Finset.mem_insert, RawStore.mem_abs, RawStore.mem_abs, hmap]
  constructor
  · rintro ⟨k, r', hk, rfl⟩
    rw [Std.ExtTreeMap.getElem?_insert] at hk
    split at hk
    · cases hk; exact Or.inl rfl
    · exact Or.inr ⟨k, r', hk, rfl⟩
  · rintro (rfl | ⟨k, r', hk, rfl⟩)
    · exact ⟨d, r, by simp, rfl⟩
    · by_cases hkd : k = d
      · subst hkd
        have := hold r' hk
        subst this
        exact ⟨k, r', by simp, rfl⟩
      · refine ⟨k, r', ?_, rfl⟩
        have hne : compare d k ≠ .eq := by rw [Ne, Digest.compare_eq_iff]; exact Ne.symm hkd
        simp only [Std.ExtTreeMap.getElem?_insert, hne, ↓reduceIte, hk]

/-! ## Equal records, equal stores -/

namespace CheckedStore

/-- A stored record, by digest: `c.raw.map[k]? = some r` exactly when the spec store holds
`toSpec r` and `k` is its digest. -/
theorem getElem?_eq_some_iff (c : CheckedStore) {k : Digest} {r : Rec} :
    c.raw.map[k]? = some r ↔ toSpec r ∈ abs c ∧ hashRecord r = k := by
  constructor
  · intro hk
    exact ⟨RawStore.mem_abs.mpr ⟨k, r, hk, rfl⟩, c.built.hash_eq k r hk⟩
  · rintro ⟨hr, rfl⟩
    exact c.built.toSpec_mem_abs.mp hr

/-- **Two stores of one chat that hold the same records are equal.** The map is fixed by the
records (each under its digest), and the heads by the map. -/
theorem eq_of_abs {c d : CheckedStore} (hg : c.group = d.group) (h : abs c = abs d) : c = d := by
  have hmap : c.raw.map = d.raw.map := by
    apply Std.ExtTreeMap.ext_getElem?
    intro k
    apply Option.ext
    intro r
    rw [c.getElem?_eq_some_iff, d.getElem?_eq_some_iff, h]
  have hheads : c.raw.heads = d.raw.heads := by
    apply Std.ExtTreeSet.ext_mem
    intro x
    rw [c.built.heads_iff, d.built.heads_iff, hmap]
  apply ext
  have hg' : c.raw.group = d.raw.group := hg
  cases hc : c.raw
  cases hd : d.raw
  rw [hc, hd] at hg' hmap hheads
  simp only at hg' hmap hheads
  rw [hg', hmap, hheads]

example : CheckedStore.empty Examples.group = CheckedStore.empty Examples.group :=
  eq_of_abs rfl rfl

/-! ## Observers -/

/-- **`heads` is the spec's heads.** -/
theorem heads_eq (c : CheckedStore) : c.heads.toList.toFinset = Crdt.Merkle.heads hashSpec (abs c) :=
  c.heads_toFinset

/-- `headsArray` (what `HEADS` replies) holds the spec's heads. -/
theorem headsArray_eq (c : CheckedStore) :
    c.headsArray.toList.toFinset = Crdt.Merkle.heads hashSpec (abs c) := by
  simp only [headsArray, List.toList_toArray]
  exact c.heads_eq

example : (CheckedStore.empty Examples.group).heads.toList.toFinset =
    Crdt.Merkle.heads hashSpec (abs (CheckedStore.empty Examples.group)) :=
  heads_eq _

/-- **`has` asks the spec store.** `c.has d` is true exactly when the spec store holds a record
whose digest is `d`. -/
theorem has_iff (c : CheckedStore) {d : Digest} :
    c.has d = true ↔ d ∈ digests hashSpec (abs c) := by
  rw [has, Std.ExtTreeMap.contains_iff_mem, c.built.mem_map_iff]
  rfl

example : Examples.s1.has (hashRecord Examples.a1) = true ↔
    hashRecord Examples.a1 ∈ digests hashSpec (abs Examples.s1) :=
  has_iff _

/-- **`get` reads the spec store.** `c.get d = some r` exactly when the spec store holds
`toSpec r` and its digest is `d`. -/
theorem get_eq_some_iff (c : CheckedStore) {d : Digest} {r : Rec} :
    c.get d = some r ↔ toSpec r ∈ abs c ∧ hashRecord r = d :=
  c.getElem?_eq_some_iff

/-- `get` finds nothing exactly when no spec record has that digest. -/
theorem get_eq_none_iff (c : CheckedStore) {d : Digest} :
    c.get d = none ↔ d ∉ digests hashSpec (abs c) := by
  rw [c.mem_digests_abs, Std.ExtTreeMap.mem_iff_isSome_getElem?, get]
  cases c.raw.map[d]? <;> simp

/-! ## Accept, case by case -/

/-- In the `accepted` case, every link of the record was already stored. -/
theorem rawAccept_accepted_links {c c' : RawStore} (hc : Built c) {r : Rec} {d : Digest}
    (h : rawAccept c r = (.accepted d, c')) : ∀ l ∈ r.links, l ∈ c.map := by
  unfold rawAccept at h
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
        have : l ∈ missingLinks c.map r := mem_missingLinks.mpr ⟨hl, hn⟩
        simp_all
      · simp at h

/-- **Accepted.** The new spec store is the spec's `accept` of the record, and `d` is the
record's digest. -/
theorem abs_accept_accepted {c c' : CheckedStore} {r : Rec} {d : Digest}
    (h : c.accept r = (.accepted d, c')) :
    abs c' = Crdt.Merkle.accept hashSpec (abs c) (toSpec r) ∧ d = hashRecord r := by
  have hraw : rawAccept c.raw r = (.accepted d, c'.raw) := by
    have e : rawAccept c.raw r = ((c.accept r).1, (c.accept r).2.raw) := rfl
    rw [e, h]
  obtain ⟨hd, _, hmap, hold⟩ := rawAccept_accepted hraw
  have hlinks := rawAccept_accepted_links c.built hraw
  refine ⟨?_, hd⟩
  rw [accept_of_resolves]
  · exact RawStore.abs_insert hmap hold
  · intro l hl
    rw [mem_toSpec_links] at hl
    exact c.built.mem_digests_abs.mpr (hlinks l hl)

/-- **Missing.** The store is unchanged, and so is the spec store under the spec's `accept`. The
list is exactly the links of the record that no spec record has as digest (sound and
complete), it is not empty, and it is sorted. -/
theorem abs_accept_missing {c c' : CheckedStore} {r : Rec} {ds : Array Digest}
    (h : c.accept r = (.missing ds, c')) :
    c' = c ∧ Crdt.Merkle.accept hashSpec (abs c) (toSpec r) = abs c ∧ ds ≠ #[] ∧
      (∀ x, x ∈ ds ↔ x ∈ (toSpec r).links ∧ x ∉ digests hashSpec (abs c)) ∧ StrictlySorted ds := by
  have hraw : rawAccept c.raw r = (.missing ds, c'.raw) := by
    have e : rawAccept c.raw r = ((c.accept r).1, (c.accept r).2.raw) := rfl
    rw [e, h]
  obtain ⟨hc, hne, hmem, hsort⟩ := rawAccept_missing hraw
  have hmem' : ∀ x, x ∈ ds ↔ x ∈ (toSpec r).links ∧ x ∉ digests hashSpec (abs c) := by
    intro x
    rw [hmem, mem_toSpec_links, c.mem_digests_abs]
  refine ⟨ext hc, ?_, hne, hmem', hsort⟩
  obtain ⟨x, hx⟩ : ∃ x, x ∈ ds := by
    rcases ds with ⟨_ | ⟨x, _⟩⟩
    · exact absurd rfl hne
    · exact ⟨x, by simp⟩
  have := (hmem' x).mp hx
  simp only [Crdt.Merkle.accept, ite_eq_right_iff]
  intro hsub
  exact absurd (hsub this.1) this.2

/-- **Collision.** The store is unchanged; `d` is the record's digest, and the spec store holds a
different record with that digest. -/
theorem abs_accept_collision {c c' : CheckedStore} {r : Rec} {d : Digest}
    (h : c.accept r = (.collision d, c')) :
    c' = c ∧ d = hashRecord r ∧ ∃ x ∈ abs c, hashSpec x = d ∧ x ≠ toSpec r := by
  have hraw : rawAccept c.raw r = (.collision d, c'.raw) := by
    have e : rawAccept c.raw r = ((c.accept r).1, (c.accept r).2.raw) := rfl
    rw [e, h]
  obtain ⟨hc, hd, old, hold, hne⟩ := rawAccept_collision hraw
  refine ⟨ext hc, hd, toSpec old, RawStore.mem_abs.mpr ⟨d, old, hold, rfl⟩, ?_, ?_⟩
  · rw [hashSpec_toSpec]; exact c.built.hash_eq d old hold
  · exact fun he => hne (toSpec_injective he)

/-- So a `collision` result is a collision in the spec store with the record added. -/
theorem collisionIn_of_accept_collision {c c' : CheckedStore} {r : Rec} {d : Digest}
    (h : c.accept r = (.collision d, c')) : CollisionIn hashSpec (insert (toSpec r) (abs c)) := by
  obtain ⟨_, rfl, x, hx, he, hne⟩ := abs_accept_collision h
  exact CollisionIn.of_mem hashSpec (Finset.mem_insert_of_mem hx) (Finset.mem_insert_self _ _) hne
    (by rw [he, hashSpec_toSpec])

/-- **Wrong chat.** The store is unchanged, and the record's chat is not the store's. -/
theorem abs_accept_wrongChat {c c' : CheckedStore} {r : Rec}
    (h : c.accept r = (.wrongChat, c')) : c' = c ∧ r.group ≠ c.group := by
  have hraw : rawAccept c.raw r = (.wrongChat, c'.raw) := by
    have e : rawAccept c.raw r = ((c.accept r).1, (c.accept r).2.raw) := rfl
    rw [e, h]
  obtain ⟨hc, hg⟩ := rawAccept_wrongChat hraw
  exact ⟨ext hc, hg⟩

/-- **Too large.** The store is unchanged, and the record has too many links, or it is new and
the store is full. -/
theorem abs_accept_tooLarge {c c' : CheckedStore} {r : Rec}
    (h : c.accept r = (.tooLarge, c')) :
    c' = c ∧ (¬ r.WellSized ∨
      (hashRecord r ∉ digests hashSpec (abs c) ∧ maxRecords ≤ c.size + 1)) := by
  have hraw : rawAccept c.raw r = (.tooLarge, c'.raw) := by
    have e : rawAccept c.raw r = ((c.accept r).1, (c.accept r).2.raw) := rfl
    rw [e, h]
  obtain ⟨hc, hw⟩ := rawAccept_tooLarge hraw
  refine ⟨ext hc, ?_⟩
  rcases hw with hw | ⟨hn, hs⟩
  · exact Or.inl hw
  · exact Or.inr ⟨by rwa [c.mem_digests_abs], hs⟩

example : abs Examples.s1 = Crdt.Merkle.accept hashSpec
      (abs (CheckedStore.empty Examples.group)) (toSpec Examples.a1) ∧
    hashRecord Examples.a1 = hashRecord Examples.a1 :=
  abs_accept_accepted (c := CheckedStore.empty Examples.group) (c' := Examples.s1) (by
    show (CheckedStore.empty Examples.group).accept Examples.a1 =
      (.accepted (hashRecord Examples.a1), Examples.s1)
    rfl)

/-! ## Merge -/

/-- **A merged store holds the records of both stores.** -/
theorem abs_merge {c d e : CheckedStore} (h : c.merge d = .ok e) : abs e = abs c ∪ abs d := by
  obtain ⟨_, hiff⟩ := merge_ok h
  ext x
  rw [Finset.mem_union, mem_abs, mem_abs, mem_abs]
  constructor
  · rintro ⟨k, r, hk, rfl⟩
    rcases (hiff k r).mp hk with hc | hd
    · exact Or.inl ⟨k, r, hc, rfl⟩
    · exact Or.inr ⟨k, r, hd, rfl⟩
  · rintro (⟨k, r, hk, rfl⟩ | ⟨k, r, hk, rfl⟩)
    · exact ⟨k, r, (hiff k r).mpr (Or.inl hk), rfl⟩
    · exact ⟨k, r, (hiff k r).mpr (Or.inr hk), rfl⟩

/-! ## Encode -/

/-- **A store reopens as itself** (exact: the maps are extensional). -/
theorem encode_open (c : CheckedStore) : CheckedStore.open c.group c.encode = .ok c :=
  encode_reopens c

end CheckedStore

end Zrdt
