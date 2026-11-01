/-
Copyright (c) 2026 zrdt contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: zrdt contributors
-/
import Mathlib
import Crdt.Merkle.ClassifyFast

set_option linter.unusedSectionVars false

/-!
# `CLASSIFY` computes the spec's `status` (docs/PLAN.md §3.5)

`ClassifyFast.lean` proves that `classify` gives each stored record a status that means what
`StatusMeans` says. This file connects that to the spec's own function, `Crdt.Merkle.status`
(`Chat.lean`), which names one holder: the smallest (lead decision 1 of 2026-11-01). So the
advertised `classify_spec` (`Api.lean`) can say, with no restatement in between:

  `classify` at digest `d` is the spec's `status` of the record stored under `d`.

* `Aci.instLinearOrder`: account ids are ordered byte by byte, the order the code's `compare`
  uses. The spec's `status` takes the smallest holder in this order.
* `Zrdt.Status.toSpec`: the code's status as the spec's status (the same label).
* `statusMeans_iff_status`: `StatusMeans` holds exactly for the spec's `status`.
* `CheckedStore.classify_toSpec`, `CheckedStore.classify_eq_some_iff`: `classify` computes the
  spec's `status`.
-/

namespace Zrdt

open Crdt.Merkle

/-! ## The order on account ids -/

/-- An account id compares equal to itself. -/
theorem Aci.compare_self (a : Aci) : compare a a = .eq :=
  Std.ReflCmp.compare_self (cmp := (compare : Aci → Aci → Ordering))

/-- Swapping the arguments of `compare` swaps the result. -/
theorem Aci.compare_swap (a b : Aci) : compare b a = (compare a b).swap :=
  Std.OrientedCmp.eq_swap (cmp := (compare : Aci → Aci → Ordering))

/-- Account ids that compare equal are equal. -/
theorem Aci.eq_of_compare {a b : Aci} (h : compare a b = .eq) : a = b :=
  Std.LawfulEqCmp.eq_of_compare (cmp := (compare : Aci → Aci → Ordering)) h

/-- Account ids are linearly ordered byte by byte. This is the order the shipped code uses
(`compare`), so `a ≤ b` exactly when `compare a b ≠ .gt` (`Aci.le_iff_compare`). -/
instance Aci.instLinearOrder : LinearOrder Aci where
  le a b := compare a b ≠ .gt
  lt a b := compare a b = .lt
  le_refl a := by
    show compare a a ≠ .gt
    rw [Aci.compare_self]; decide
  le_trans a b c h₁ h₂ :=
    Std.TransCmp.le_trans (cmp := (compare : Aci → Aci → Ordering)) h₁ h₂
  lt_iff_le_not_ge a b := by
    show compare a b = .lt ↔ compare a b ≠ .gt ∧ ¬ compare b a ≠ .gt
    rw [Aci.compare_swap a b]
    cases compare a b <;> decide
  le_antisymm a b h₁ h₂ := by
    change compare a b ≠ .gt at h₁
    change compare b a ≠ .gt at h₂
    rw [Aci.compare_swap a b] at h₂
    apply Aci.eq_of_compare
    cases h : compare a b <;> simp_all
  le_total a b := by
    show compare a b ≠ .gt ∨ compare b a ≠ .gt
    rw [Aci.compare_swap a b]
    cases compare a b <;> decide
  toDecidableLE a b := inferInstanceAs (Decidable (compare a b ≠ .gt))
  toDecidableEq := inferInstance
  toDecidableLT a b := inferInstanceAs (Decidable (compare a b = .lt))
  compare a b := compare a b
  compare_eq_compareOfLessAndEq a b := by
    show compare a b = if compare a b = .lt then .lt else if a = b then .eq else .gt
    cases h : compare a b
    · simp
    · simp [Aci.eq_of_compare h]
    · have hne : a ≠ b := by
        rintro rfl; rw [Aci.compare_self] at h; cases h
      simp [hne]

/-- `≤` on account ids is the code's `compare a b ≠ .gt`. -/
theorem Aci.le_iff_compare {a b : Aci} : a ≤ b ↔ compare a b ≠ .gt := Iff.rfl

-- Alice's id (all bytes `0xa1`) is below Bob's (all bytes `0xb0`).
example : Examples.alice < Examples.bob := by decide +kernel

/-! ## The code's status as the spec's status -/

/-- The code's status (`Zrdt.Status`, what `CLASSIFY` replies) as the spec's status
(`Crdt.Merkle.Status Aci`): the same label, and for `heldBy` the same member. -/
def Status.toSpec : Zrdt.Status → Crdt.Merkle.Status Aci
  | .confirmedByAuthor => .confirmedByAuthor
  | .notConfirmedByAuthor => .notConfirmedByAuthor
  | .heldBy a => .heldBy a
  | .unconfirmed => .unconfirmed

example : (Zrdt.Status.heldBy Examples.bob).toSpec = .heldBy Examples.bob := rfl

/-- Different code statuses are different spec statuses. -/
theorem Status.toSpec_injective : Function.Injective Status.toSpec := by
  intro a b h
  cases a <;> cases b <;> simp_all [Status.toSpec]

/-- **`StatusMeans` is the spec's `status`.** The status `st` means, for record `x`, what
`StatusMeans` says exactly when the spec's `status` of `x` is `st`. -/
theorem statusMeans_iff_status (s : SpecStore) (P : LiveFacts Digest) (x : SpecRec)
    (st : Zrdt.Status) : StatusMeans s P x st ↔ Crdt.Merkle.status hashSpec s P x = st.toSpec := by
  unfold Crdt.Merkle.status
  split_ifs with hA hF hH
  · cases st <;> simp [StatusMeans, Status.toSpec, hA]
  · cases st <;> simp [StatusMeans, Status.toSpec, hA, hF]
  · cases st with
    | heldBy a =>
      simp only [StatusMeans, Status.toSpec, hA, hF, not_false_eq_true, true_and,
        Crdt.Merkle.Status.heldBy.injEq]
      constructor
      · rintro ⟨ha, hle⟩
        exact le_antisymm (Finset.min'_le _ a ha) (Finset.le_min' _ hH a hle)
      · rintro rfl
        exact ⟨Finset.min'_mem _ hH, fun b hb => Finset.min'_le _ b hb⟩
    | unconfirmed =>
      simp only [StatusMeans, Status.toSpec, reduceCtorEq, iff_false]
      rintro ⟨-, -, he⟩
      rw [he] at hH
      exact Finset.not_nonempty_empty hH
    | confirmedByAuthor => simp [StatusMeans, Status.toSpec, hA]
    | notConfirmedByAuthor => simp [StatusMeans, Status.toSpec, hF]
  · rw [Finset.not_nonempty_iff_eq_empty] at hH
    cases st <;> simp [StatusMeans, Status.toSpec, hA, hF, hH]

-- With no live record at all, the spec's status of every record is `unconfirmed`.
example (x : SpecRec) : Crdt.Merkle.status hashSpec ∅ ⟨∅, ∅⟩ x = .unconfirmed :=
  (statusMeans_iff_status ∅ ⟨∅, ∅⟩ x .unconfirmed).mp
    (by simp [StatusMeans, authorConfirmed, foreignMarked, holders, liveRecords])

/-! ## `classify` computes the spec's `status` -/

/-- **`classify` computes the spec's `status`.** At every digest `d`, the status `classify`
gives (read as the spec's status) is the spec's `status` of the record stored under `d`; and
`classify` gives no status where no record is stored. -/
theorem CheckedStore.classify_toSpec (c : CheckedStore) (facts : Array Fact) (d : Digest) :
    ((classify c facts)[d]?).map Status.toSpec =
      (c.get d).map fun r => Crdt.Merkle.status hashSpec (abs c) (liveOf facts) (toSpec r) := by
  cases hc : (classify c facts)[d]? with
  | none =>
    cases hr : c.get d with
    | none => rfl
    | some r =>
      obtain ⟨st, hst⟩ : ∃ st, (classify c facts)[d]? = some st := by
        rw [classify, Std.ExtTreeMap.getElem?_map, show c.raw.map[d]? = some r from hr]
        exact ⟨_, rfl⟩
      rw [hc] at hst
      cases hst
  | some st =>
    obtain ⟨r, hr, hs⟩ := (classify_getElem?_iff c facts d st).mp hc
    rw [hr, Option.map_some, Option.map_some, (statusMeans_iff_status _ _ _ _).mp hs]

/-- **`classify`, digest by digest.** `classify c facts` gives digest `d` the status `st` exactly
when `d` is the digest of a stored record `r` and the spec's `status` of `r` is `st`
(advertised as `CheckedStore.classify_spec` in `Api.lean`). -/
theorem CheckedStore.classify_eq_some_iff (c : CheckedStore) (facts : Array Fact) (d : Digest)
    (st : Zrdt.Status) :
    (classify c facts)[d]? = some st ↔
      ∃ r, c.get d = some r ∧
        Crdt.Merkle.status hashSpec (abs c) (liveOf facts) (toSpec r) = st.toSpec := by
  simp only [classify_getElem?_iff, statusMeans_iff_status]

/-- `s1` holds `a1` under its digest (computed by the kernel). -/
theorem Examples.s1_get_a1 : Examples.s1.get (hashRecord Examples.a1) = some Examples.a1 := by
  decide +kernel

-- On a concrete store: with no facts, `classify s1` at `a1`'s digest is the spec's status of
-- `a1`, which is `unconfirmed`.
example : ((classify Examples.s1 #[])[hashRecord Examples.a1]?).map Status.toSpec =
    some .unconfirmed := by
  rw [CheckedStore.classify_toSpec, Examples.s1_get_a1, Option.map_some]
  simp [Crdt.Merkle.status, authorConfirmed, foreignMarked, holders, liveRecords, liveOf, liveList]

end Zrdt
