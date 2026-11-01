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
* `acceptAll` (`abs_acceptAll`): a batch adds only its own records, keeps the store's, and each
  record left over is refused by the spec's `accept` (or by a collision, the chat, or size).
* `merge` (`merge_abs`): a merged store holds the records of both stores.
* `heads` (`heads_eq`), `has` (`has_iff`), `get` (`get_eq_some_iff`): the observers read the spec
  store.
* `reachSet` (`reachSet_iff`): the walk finds exactly the digests of the spec's `reachSet`
  (`mem_walk_iff`: the link walk is right). `confirmed_records`: what a live message's links
  reach is the same, record for record, in your store and the sender's (via `confirmed_exact`).
* `eq_of_abs`: two stores of one chat that hold the same records are equal.

`open` and `salvage` over the model (`open_iff`, `salvage_spec`) are in `LoadApi.lean` (lane
build/encode-proofs-api), built on `specOf` and the lemmas here; `encode` is core's
`encode_reopens`.

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

/-! ## The link walk -/

/-- `WalkReach m next S d`: starting from the digests `S` and following, from each key `k` of `m`
that is reached, the digests `next m[k]`, you get to `d`. This is what `walk` computes
(`mem_walk_iff`); a start digest or a link that is not a key is reached but leads nowhere. -/
inductive WalkReach {β : Type} (m : Std.ExtTreeMap Digest β compare) (next : β → List Digest)
    (S : List Digest) : Digest → Prop
  /-- Every start digest is reached. -/
  | start {d : Digest} : d ∈ S → WalkReach m next S d
  /-- From a reached key, each digest `next` gives for its value is reached. -/
  | step {k d : Digest} {v : β} : WalkReach m next S k → m[k]? = some v → d ∈ next v →
      WalkReach m next S d

example : WalkReach (∅ : Std.ExtTreeMap Digest Nat compare) (fun _ => []) [Examples.dig 1]
    (Examples.dig 1) := .start (List.mem_singleton_self _)

/-- What stays true while `walk` runs over `m` from the start digests `S`: `left` is `m` without
the visited keys; every visited key is a key of `m` and reached; every digest still to do is
reached; and every link of a visited key, and every start digest, is visited, still to do, or not
a key of `m`. -/
structure WalkInv {β : Type} (m : Std.ExtTreeMap Digest β compare) (next : β → List Digest)
    (S : List Digest) (left : Std.ExtTreeMap Digest β compare) (seen : DigestSet)
    (todo : List Digest) : Prop where
  left_seen : ∀ k, k ∈ seen → left[k]? = none
  left_other : ∀ k, k ∉ seen → left[k]? = m[k]?
  seen_ok : ∀ k ∈ seen, k ∈ m ∧ WalkReach m next S k
  todo_ok : ∀ d ∈ todo, WalkReach m next S d
  seen_closed : ∀ k ∈ seen, ∀ v, m[k]? = some v → ∀ d ∈ next v, d ∈ seen ∨ d ∈ todo ∨ d ∉ m
  start_ok : ∀ d ∈ S, d ∈ seen ∨ d ∈ todo ∨ d ∉ m

/-- `walk` from a state that satisfies the invariant returns exactly the reached keys of `m`. -/
theorem walk_spec {β : Type} (m : Std.ExtTreeMap Digest β compare) (next : β → List Digest)
    (S : List Digest) (left : Std.ExtTreeMap Digest β compare) (seen : DigestSet)
    (todo : List Digest) (hI : WalkInv m next S left seen todo) :
    ∀ d, d ∈ walk next left seen todo ↔ d ∈ m ∧ WalkReach m next S d := by
  induction left, seen, todo using walk.induct next with
  | case1 left seen =>
    intro d
    rw [walk]
    have key : ∀ d, WalkReach m next S d → d ∈ m → d ∈ seen := by
      intro d hR
      induction hR with
      | start hd =>
        intro hdm
        rcases hI.start_ok _ hd with h | h | h
        · exact h
        · simp at h
        · exact absurd hdm h
      | @step k d v _ hkv hd ih =>
        intro hdm
        have hkm : k ∈ m := Std.ExtTreeMap.mem_iff_isSome_getElem?.mpr (by simp [hkv])
        rcases hI.seen_closed k (ih hkm) v hkv d hd with h | h | h
        · exact h
        · simp at h
        · exact absurd hdm h
    exact ⟨hI.seen_ok d, fun ⟨hdm, hR⟩ => key d hR hdm⟩
  | case2 left seen d todo h ih =>
    intro x
    rw [walk, dite_eq_left_of_eq_true (eq_true h)]
    apply ih
    have hdseen : d ∉ seen := fun hs => by
      have := hI.left_seen d hs
      rw [Std.ExtTreeMap.mem_iff_isSome_getElem?, this] at h
      simp at h
    have hv : m[d]? = some (left.get d h) := by
      rw [← hI.left_other d hdseen, Std.ExtTreeMap.get_eq_getElem]
      exact Std.ExtTreeMap.getElem?_eq_some_getElem h
    have hdm : d ∈ m := Std.ExtTreeMap.mem_iff_isSome_getElem?.mpr (by simp [hv])
    have hRd : WalkReach m next S d := hI.todo_ok d List.mem_cons_self
    have mem_ins : ∀ k, k ∈ seen.insert d ↔ k = d ∨ k ∈ seen := fun k => by
      rw [Std.ExtTreeSet.mem_insert, Digest.compare_eq_iff, eq_comm]
    refine ⟨fun k hk => ?_, fun k hk => ?_, fun k hk => ?_, fun k hk => ?_,
      fun k hk v hv' y hy => ?_, fun y hy => ?_⟩
    · rw [Std.ExtTreeMap.getElem?_erase]
      rcases (mem_ins k).mp hk with rfl | hk
      · simp
      · split
        · rfl
        · exact hI.left_seen k hk
    · rw [mem_ins, not_or] at hk
      have hne : compare d k ≠ .eq := by rw [Ne, Digest.compare_eq_iff]; exact Ne.symm hk.1
      simp only [Std.ExtTreeMap.getElem?_erase, hne, ↓reduceIte]
      exact hI.left_other k hk.2
    · rcases (mem_ins k).mp hk with rfl | hk
      · exact ⟨hdm, hRd⟩
      · exact hI.seen_ok k hk
    · rcases List.mem_append.mp hk with hk | hk
      · exact .step hRd hv hk
      · exact hI.todo_ok k (List.mem_cons_of_mem _ hk)
    · rcases (mem_ins k).mp hk with rfl | hk
      · rw [hv] at hv'
        cases hv'
        exact Or.inr (Or.inl (List.mem_append_left _ hy))
      · rcases hI.seen_closed k hk v hv' y hy with h' | h' | h'
        · exact Or.inl ((mem_ins y).mpr (Or.inr h'))
        · rcases List.mem_cons.mp h' with rfl | h'
          · exact Or.inl ((mem_ins y).mpr (Or.inl rfl))
          · exact Or.inr (Or.inl (List.mem_append_right _ h'))
        · exact Or.inr (Or.inr h')
    · rcases hI.start_ok y hy with h' | h' | h'
      · exact Or.inl ((mem_ins y).mpr (Or.inr h'))
      · rcases List.mem_cons.mp h' with rfl | h'
        · exact Or.inl ((mem_ins y).mpr (Or.inl rfl))
        · exact Or.inr (Or.inl (List.mem_append_right _ h'))
      · exact Or.inr (Or.inr h')
  | case3 left seen d todo h ih =>
    intro x
    rw [walk, dite_eq_right_of_eq_false (eq_false h)]
    apply ih
    have hd : d ∈ seen ∨ d ∉ m := by
      by_cases hs : d ∈ seen
      · exact Or.inl hs
      · refine Or.inr fun hm => h ?_
        rw [Std.ExtTreeMap.mem_iff_isSome_getElem?, hI.left_other d hs]
        exact Std.ExtTreeMap.mem_iff_isSome_getElem?.mp hm
    refine ⟨hI.left_seen, hI.left_other, hI.seen_ok,
      fun k hk => hI.todo_ok k (List.mem_cons_of_mem _ hk), fun k hk v hv y hy => ?_,
      fun y hy => ?_⟩
    · rcases hI.seen_closed k hk v hv y hy with h' | h' | h'
      · exact Or.inl h'
      · rcases List.mem_cons.mp h' with rfl | h'
        · rcases hd with hd | hd
          · exact Or.inl hd
          · exact Or.inr (Or.inr hd)
        · exact Or.inr (Or.inl h')
      · exact Or.inr (Or.inr h')
    · rcases hI.start_ok y hy with h' | h' | h'
      · exact Or.inl h'
      · rcases List.mem_cons.mp h' with rfl | h'
        · rcases hd with hd | hd
          · exact Or.inl hd
          · exact Or.inr (Or.inr hd)
        · exact Or.inr (Or.inl h')
      · exact Or.inr (Or.inr h')

/-- **The walk is right.** Walking `m` from the start digests `S` returns exactly the keys of `m`
that are reached from `S`. -/
theorem mem_walk_iff {β : Type} (m : Std.ExtTreeMap Digest β compare) (next : β → List Digest)
    (S : List Digest) {d : Digest} :
    d ∈ walk next m ∅ S ↔ d ∈ m ∧ WalkReach m next S d :=
  walk_spec m next S m ∅ S
    ⟨fun _ hk => absurd hk Std.ExtTreeSet.not_mem_empty, fun _ _ => rfl,
      fun _ hk => absurd hk Std.ExtTreeSet.not_mem_empty, fun _ hd => .start hd,
      fun _ hk => absurd hk Std.ExtTreeSet.not_mem_empty, fun _ hd => Or.inr (Or.inl hd)⟩ d

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
theorem heads_eq (c : CheckedStore) :
    c.heads.toList.toFinset = Crdt.Merkle.heads hashSpec (abs c) :=
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

/-! ## Reachability -/

/-- On a checked store, the walk's reachability is the spec's `Reach`, started from the same
digests. -/
theorem walkReach_iff (c : CheckedStore) (hs : Array Digest) {d : Digest} :
    WalkReach c.raw.map (fun r => r.links.toList) hs.toList d ↔
      Reach hashSpec (abs c) hs.toList.toFinset d := by
  constructor
  · intro h
    induction h with
    | start hd => exact .head (List.mem_toFinset.mpr hd)
    | @step k d v _ hkv hd ih =>
      refine .link (r := toSpec v) (RawStore.mem_abs.mpr ⟨k, v, hkv, rfl⟩) ?_
        (mem_toSpec_links.mpr (Array.mem_toList_iff.mp hd))
      rwa [hashSpec_toSpec, c.built.hash_eq k v hkv]
  · intro h
    induction h with
    | head hd => exact .start (List.mem_toFinset.mp hd)
    | @link x d hx _ hl ih =>
      obtain ⟨v, rfl, hv⟩ := c.built.exists_of_mem_abs hx
      rw [hashSpec_toSpec] at ih
      exact .step ih hv (Array.mem_toList_iff.mpr (mem_toSpec_links.mp hl))

/-- **`reachSet` is the spec's `reachSet`.** A digest is in `c.reachSet hs` exactly when it is
the digest of a record in the spec's `reachSet` of `abs c` from `hs`: a stored record reached by
following links from `hs`. -/
theorem reachSet_iff (c : CheckedStore) (hs : Array Digest) {d : Digest} :
    d ∈ c.reachSet hs ↔
      d ∈ digests hashSpec (Crdt.Merkle.reachSet hashSpec (abs c) hs.toList.toFinset) := by
  rw [reachSet, mem_walk_iff, walkReach_iff, mem_digests]
  constructor
  · rintro ⟨hdm, hR⟩
    obtain ⟨x, hx, rfl⟩ := (mem_digests hashSpec).mp (c.mem_digests_abs.mpr hdm)
    exact ⟨x, (mem_reachSet hashSpec).mpr ⟨hx, hR⟩, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨hx, hR⟩ := (mem_reachSet hashSpec).mp hx
    exact ⟨c.mem_digests_abs.mp ((mem_digests hashSpec).mpr ⟨x, hx, rfl⟩), hR⟩

/-- `reachSet` as a finite set of digests. -/
theorem reachSet_toFinset (c : CheckedStore) (hs : Array Digest) :
    (c.reachSet hs).toList.toFinset =
      digests hashSpec (Crdt.Merkle.reachSet hashSpec (abs c) hs.toList.toFinset) := by
  ext d
  rw [List.mem_toFinset, Std.ExtTreeSet.mem_toList, reachSet_iff]

/-- **Confirmation is exact** (docs/PLAN.md §3.2, "held by the sender"). A live message links
`hs`, and both your store `c` and the sender's store `d` hold every digest of `hs`. Then the
records the links reach are the same in both stores, digest for digest and record for record.
Or two different records, across the two stores, have the same digest. (`Api.lean` advertises
the digest form as `confirmed`; with no collision, equal digests already mean equal records.) -/
theorem confirmed_records (c d : CheckedStore) (hs : Array Digest)
    (hc : ∀ h ∈ hs, c.has h = true) (hd : ∀ h ∈ hs, d.has h = true) :
    (c.reachSet hs = d.reachSet hs ∧ ∀ k ∈ c.reachSet hs, c.get k = d.get k) ∨
      CollisionIn hashSpec (abs c ∪ abs d) := by
  have hsub : ∀ (e : CheckedStore), (∀ h ∈ hs, e.has h = true) →
      hs.toList.toFinset ⊆ digests hashSpec (abs e) := fun e he x hx =>
    (e.has_iff).mp (he x (Array.mem_toList_iff.mp (List.mem_toFinset.mp hx)))
  rcases confirmed_exact hashSpec c.closed d.closed (hsub c hc) (hsub d hd) with h | h
  · left
    refine ⟨Std.ExtTreeSet.ext_mem fun k => by rw [reachSet_iff, reachSet_iff, h], ?_⟩
    intro k hk
    rw [reachSet_iff, mem_digests] at hk
    obtain ⟨x, hx, rfl⟩ := hk
    have hx' := hx
    rw [h] at hx'
    obtain ⟨hxc, _⟩ := (mem_reachSet hashSpec).mp hx
    obtain ⟨hxd, _⟩ := (mem_reachSet hashSpec).mp hx'
    obtain ⟨r, rfl, hr⟩ := c.built.exists_of_mem_abs hxc
    rw [hashSpec_toSpec]
    rw [get, get, hr, d.built.toSpec_mem_abs.mp hxd]
  · right
    exact CollisionIn.mono hashSpec (Finset.union_subset_union (Finset.filter_subset _ _)
      (Finset.filter_subset _ _)) h

/-- `s1` (Alice's `a1`) holds `a1` (computed by the kernel). -/
theorem _root_.Zrdt.Examples.s1_has_a1 : Examples.s1.has (hashRecord Examples.a1) = true := by
  decide +kernel

/-- `s2` (`a1`, then Bob's reply `b1`) holds `a1` (computed by the kernel). -/
theorem _root_.Zrdt.Examples.s2_has_a1 : Examples.s2.has (hashRecord Examples.a1) = true := by
  decide +kernel

-- A message that links `a1` reaches the same records in `s1` and in `s2`; `b1` is not reached.
example : (Examples.s1.reachSet #[hashRecord Examples.a1] =
      Examples.s2.reachSet #[hashRecord Examples.a1] ∧
      ∀ k ∈ Examples.s1.reachSet #[hashRecord Examples.a1], Examples.s1.get k = Examples.s2.get k) ∨
    CollisionIn hashSpec (abs Examples.s1 ∪ abs Examples.s2) :=
  confirmed_records _ _ _ (fun h hh => by simp at hh; subst hh; exact Examples.s1_has_a1)
    (fun h hh => by simp at hh; subst hh; exact Examples.s2_has_a1)

example : hashRecord Examples.a1 ∈ Examples.s2.reachSet #[hashRecord Examples.a1] ↔
    hashRecord Examples.a1 ∈ digests hashSpec
      (Crdt.Merkle.reachSet hashSpec (abs Examples.s2) {hashRecord Examples.a1}) := by
  simpa using reachSet_iff Examples.s2 #[hashRecord Examples.a1]

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

/-! ## Accepting a batch -/

/-- **`acceptAll`, in the spec model.** Let `(e, left) := c.acceptAll rs`. The new spec store
keeps every record of `c` and adds only records of the batch; every batch record that is not
left over is in it; and every left-over record is from the batch and is refused by the spec's
`accept` in the final store (its links do not all resolve), unless the code refused it for a
collision, another chat, or size. -/
theorem abs_acceptAll (c : CheckedStore) (rs : Array Rec) :
    abs c ⊆ abs (c.acceptAll rs).1 ∧
    abs (c.acceptAll rs).1 ⊆ abs c ∪ specOf rs ∧
    (∀ x ∈ rs, x ∉ (c.acceptAll rs).2 → toSpec x ∈ abs (c.acceptAll rs).1) ∧
    ∀ x ∈ (c.acceptAll rs).2, x ∈ rs ∧
      (Crdt.Merkle.accept hashSpec (abs (c.acceptAll rs).1) (toSpec x) =
          abs (c.acceptAll rs).1 ∨
        CollisionIn hashSpec (insert (toSpec x) (abs (c.acceptAll rs).1)) ∨
        x.group ≠ c.group ∨ ¬ x.WellSized ∨ maxRecords ≤ (c.acceptAll rs).1.size + 1) := by
  obtain ⟨hg, hkeep, honly, hstored, hleft⟩ := acceptAll_sound c rs
  have hstuck := acceptAll_stuck c rs
  generalize c.acceptAll rs = res at hg hkeep honly hstored hleft hstuck ⊢
  obtain ⟨e, left⟩ := res
  dsimp only at hg hkeep honly hstored hleft hstuck ⊢
  refine ⟨fun x hx => ?_, fun x hx => ?_, fun x hx hl => ?_, fun x hx => ⟨hleft x hx, ?_⟩⟩
  · obtain ⟨k, r, hk, rfl⟩ := mem_abs.mp hx
    exact mem_abs.mpr ⟨k, r, hkeep k r hk, rfl⟩
  · obtain ⟨k, r, hk, rfl⟩ := mem_abs.mp hx
    rcases honly k r hk with h | h
    · exact Finset.mem_union_left _ (mem_abs.mpr ⟨k, r, h, rfl⟩)
    · exact Finset.mem_union_right _ (toSpec_mem_specOf.mpr h)
  · exact e.built.toSpec_mem_abs.mpr (hstored x hx hl)
  · have hne := hstuck x hx
    rcases hres : e.accept x with ⟨res, e'⟩
    rw [hres] at hne
    cases res with
    | accepted d => exact absurd rfl (hne d)
    | missing ds =>
      exact Or.inl (abs_accept_missing hres).2.1
    | collision d => exact Or.inr (Or.inl (collisionIn_of_accept_collision hres))
    | wrongChat =>
      exact Or.inr (Or.inr (Or.inl (by rw [← hg]; exact (abs_accept_wrongChat hres).2)))
    | tooLarge =>
      rcases (abs_accept_tooLarge hres).2 with h | ⟨-, h⟩
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr h)))

example : abs (CheckedStore.empty Examples.group) ⊆
    abs ((CheckedStore.empty Examples.group).acceptAll #[Examples.a1]).1 :=
  (abs_acceptAll _ _).1

/-! ## Merge -/

/-- **A merged store holds the records of both stores** (advertised as `abs_merge` in
`Api.lean`). -/
theorem merge_abs {c d e : CheckedStore} (h : c.merge d = .ok e) : abs e = abs c ∪ abs d := by
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

end CheckedStore

end Zrdt
