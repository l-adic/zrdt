/-
Copyright (c) 2026 zrdt contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: zrdt contributors
-/
import Mathlib
import Crdt.Merkle.Refine
import Crdt.Merkle.EncodeProofs
import Crdt.Merkle.LoadSpec

set_option linter.unusedSectionVars false

/-!
# `open_iff` and `salvage_spec` over the model (docs/PLAN.md §3.2)

The two statements about loading a store, `OPEN` and `SALVAGE`, stated over the spec model
through `abs` and `specOf`. They are assembled from:

- the code's side (`EncodeProofs.lean`, no Mathlib): `open_iff_records`, `acceptAll_closed`,
  `openRecords_eq_ok_of_stored`, `salvageRecords_ok`;
- the model's side (`LoadSpec.lean`): `buildRetry` is inside every store that takes in the batch
  (`subset_of_takesIn`, `buildRetry_eq_of_takesIn`);
- the bridge (`Bridge.lean`, `Refine.lean`): `abs`, `specOf`, `toSpec` injective, `hashSpec`.

`salvage_spec` needs no collision hypothesis: a successful salvage had none
(`salvageRecords_noCollision`), and the statement says so. This is stronger than the PLAN form
("(same hypotheses on u)").

PROPOSAL for `Api.lean` (lane P3): `Api.lean` can state these two by name, or import this file.
-/

namespace Zrdt

open Crdt.Merkle

namespace CheckedStore

/-- `toSpec r` is in a store's spec store exactly when `r` is one of its records. -/
theorem toSpec_mem_abs_iff {c : CheckedStore} {r : Rec} : toSpec r ∈ abs c ↔ r ∈ c.records := by
  rw [abs, c.built.toSpec_mem_abs, mem_records_iff]

/-- A store's spec store is `specOf u` exactly when the store holds exactly the records of `u`. -/
theorem abs_eq_specOf_iff {c : CheckedStore} {u : Array Rec} :
    abs c = specOf u ↔ ∀ x, x ∈ c.records ↔ x ∈ u := by
  constructor
  · intro h x
    rw [← toSpec_mem_abs_iff, h, toSpec_mem_specOf]
  · intro h
    ext y
    constructor
    · intro hy
      obtain ⟨r, rfl, hr⟩ := c.built.exists_of_mem_abs hy
      exact toSpec_mem_specOf.mpr ((h r).mp (mem_records_iff.mpr hr))
    · intro hy
      obtain ⟨r, hr, rfl⟩ := mem_specOf.mp hy
      exact toSpec_mem_abs_iff.mpr ((h r).mpr hr)

example (c : CheckedStore) : abs c = specOf c.records := abs_eq_specOf_iff.mpr fun _ => Iff.rfl

/-- No collision in the model means no collision among the records. -/
theorem noCollision_of_specOf {u : Array Rec} (h : ¬ CollisionIn hashSpec (specOf u)) :
    NoCollision u := by
  intro x hx y hy hxy
  refine Classical.byContradiction fun hne => h ?_
  exact ⟨toSpec x, toSpec_mem_specOf.mpr hx, toSpec y, toSpec_mem_specOf.mpr hy,
    fun he => hne (toSpec_injective he), by simpa using hxy⟩

/-- A store takes in `specOf u` (in the model's sense) when it holds every record of `u` whose
links are all digests of its records. -/
theorem takesIn_of_closed {c : CheckedStore} {u : Array Rec}
    (h : ∀ r ∈ u, (∀ d ∈ r.links, ∃ x ∈ c.records, hashRecord x = d) → r ∈ c.records) :
    ∀ R ∈ specOf u, R.links ⊆ digests hashSpec (abs c) → R ∈ abs c := by
  intro R hR hl
  obtain ⟨r, hr, rfl⟩ := mem_specOf.mp hR
  apply toSpec_mem_abs_iff.mpr
  apply h r hr
  intro d hd
  have := hl (mem_toSpec_links.mpr hd)
  rw [mem_digests_abs] at this
  exact mem_map_iff_records.mp this

/-- **`open`, over the model.** `open g b` returns the store `c` exactly when `b` decodes to chat
`g` and records `u` that are within the size limits, accept-built, free of collisions and all of
chat `g`; and `c` is the store of chat `g` holding exactly those records. -/
theorem open_iff {g : GroupId} {b : ByteArray} {c : CheckedStore} :
    CheckedStore.open g b = .ok c ↔
      ∃ u, decodeBlob b = some (g, u) ∧ WellSized u ∧ AcceptBuilt hashSpec (specOf u) ∧
        ¬ CollisionIn hashSpec (specOf u) ∧ (∀ r ∈ u, r.group = g) ∧ abs c = specOf u ∧
        c.group = g := by
  constructor
  · intro h
    obtain ⟨u, hdec, hw, hg, -, -, hcg, hrec⟩ := open_iff_records.mp h
    have habs := abs_eq_specOf_iff.mpr hrec
    have hnc : ¬ CollisionIn hashSpec (abs c) := c.built.no_collision
    exact ⟨u, hdec, hw, habs ▸ c.acceptBuilt, habs ▸ hnc, hg, habs, hcg⟩
  · rintro ⟨u, hdec, hw, hab, hncol, hg, habs, hcg⟩
    have hcol := noCollision_of_specOf hncol
    have hsub := subset_of_takesIn hashSpec hab (takesIn_of_closed (acceptAll_closed hw hg hcol))
    have hall : ∀ r ∈ u, r ∈ ((empty g).acceptAll u).1.records := fun r hr =>
      toSpec_mem_abs_iff.mp (hsub (toSpec_mem_specOf.mpr hr))
    have he := openRecords_eq_ok_of_stored hw hg hall
    have hec : ((empty g).acceptAll u).1 = c := by
      apply eq_of_records (acceptAll_empty_records.1.trans hcg.symm)
      intro x
      rw [abs_eq_specOf_iff.mp habs x]
      exact ⟨fun hx => acceptAll_empty_records.2 x hx, fun hx => hall x hx⟩
    exact open_eq_ok_iff.mpr ⟨u, hdec, hec ▸ he⟩

/-- A store's own blob satisfies every condition of `open_iff`. -/
example (c : CheckedStore) : ∃ u, decodeBlob c.encode = some (c.group, u) ∧ WellSized u ∧
    AcceptBuilt hashSpec (specOf u) ∧ ¬ CollisionIn hashSpec (specOf u) ∧
    (∀ r ∈ u, r.group = c.group) ∧ abs c = specOf u ∧ c.group = c.group :=
  open_iff.mp (encode_reopens c)

/-- No collision among the records means no collision in the model. -/
theorem not_collisionIn_specOf {u : Array Rec} (h : NoCollision u) :
    ¬ CollisionIn hashSpec (specOf u) := by
  rintro ⟨X, hX, Y, hY, hne, hh⟩
  obtain ⟨x, hx, rfl⟩ := mem_specOf.mp hX
  obtain ⟨y, hy, rfl⟩ := mem_specOf.mp hY
  simp only [hashSpec_toSpec] at hh
  exact hne (congrArg toSpec (h x hx y hy hh))

/-- The model's condition rejects a bad blob: `b1` alone (its link, `a1`, cut out) is not
accept-built, so by `open_iff` no blob holding exactly `b1` opens. -/
example : ¬ AcceptBuilt hashSpec (specOf #[Examples.b1]) := by
  rintro ⟨l, -, hb⟩
  have hc : Closed hashSpec (specOf #[Examples.b1]) := hb ▸ closed_build hashSpec l
  obtain ⟨R, hR, he⟩ := hc (toSpec Examples.b1) (toSpec_mem_specOf.mpr (by simp))
    (hashRecord Examples.a1) (by simp [Examples.b1])
  obtain ⟨r, hr, rfl⟩ := mem_specOf.mp hR
  simp only [List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at hr
  subst hr
  rw [hashSpec_toSpec] at he
  revert he
  decide +kernel

/-- **`salvage`, over the model.** If `salvage g b` loads `s`, and `b` holds the records `u`, then
the records have no collision, the store holds exactly what the model's salvage `buildRetry`
keeps, it is of chat `g`, and `dropped` is sorted and holds exactly the digests of the other
records. -/
theorem salvage_spec {g : GroupId} {b : ByteArray} {s : Salvaged} {u : Array Rec}
    (h : salvage g b = .ok s) (hu : decodeBlob b = some (g, u)) :
    ¬ CollisionIn hashSpec (specOf u) ∧
      abs s.store = buildRetry hashSpec (specOf u) ∧ s.store.group = g ∧
      (∀ d, d ∈ s.dropped ↔ d ∈ digests hashSpec (specOf u \ buildRetry hashSpec (specOf u))) ∧
      StrictlySorted s.dropped := by
  obtain ⟨u', hu', hs⟩ := salvage_eq_ok_iff.mp h
  rw [hu] at hu'
  simp only [Option.some.injEq, Prod.mk.injEq, true_and] at hu'
  subst hu'
  have hcol := salvageRecords_noCollision hs
  obtain ⟨_, _, hsg, honly, hclosed, hdrop, hsorted⟩ := salvageRecords_ok hs
  have habs : abs s.store = buildRetry hashSpec (specOf u) := by
    symm
    apply buildRetry_eq_of_takesIn hashSpec
    · intro x hx
      obtain ⟨r, rfl, hr⟩ := s.store.built.exists_of_mem_abs hx
      exact toSpec_mem_specOf.mpr (honly r (mem_records_iff.mpr hr))
    · exact s.store.acceptBuilt
    · exact takesIn_of_closed (hclosed hcol)
  refine ⟨not_collisionIn_specOf hcol, habs, hsg, fun d => ?_, hsorted⟩
  rw [hdrop, ← habs, mem_digests]
  constructor
  · rintro ⟨r, hr, hn, rfl⟩
    exact ⟨toSpec r, Finset.mem_sdiff.mpr ⟨toSpec_mem_specOf.mpr hr,
      fun h => hn (toSpec_mem_abs_iff.mp h)⟩, hashSpec_toSpec r⟩
  · rintro ⟨R, hR, rfl⟩
    obtain ⟨hRu, hRn⟩ := Finset.mem_sdiff.mp hR
    obtain ⟨r, hr, rfl⟩ := mem_specOf.mp hRu
    exact ⟨r, hr, fun h => hRn (toSpec_mem_abs_iff.mpr h), (hashSpec_toSpec r).symm⟩

/-- The hypotheses of `salvage_spec` hold together: a store's own blob salvages to the same
records. -/
example (c : CheckedStore) : ∃ s, salvage c.group c.encode = .ok s ∧
    abs s.store = buildRetry hashSpec (specOf c.records) := by
  have hdec := decodeBlob_encodeBlob c.group c.records c.wellSized_records
  obtain ⟨s, hs⟩ := salvage_ok_of hdec c.wellSized_records (fun _ h => group_of_mem_records h)
    c.noCollision_records
  exact ⟨s, hs, (salvage_spec hs hdec).2.1⟩

end CheckedStore

end Zrdt
