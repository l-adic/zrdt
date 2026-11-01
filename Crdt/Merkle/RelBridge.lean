/-
Copyright (c) 2026 zrdt contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: zrdt contributors
-/
import Mathlib
import Crdt.Merkle.RelSpec
import Crdt.Merkle.Refine
import Zrdt.ChatStore

set_option linter.unusedSectionVars false

/-!
# What the statements about a store with a boundary mention (docs/JOIN_PLAN.md §7.3)

Two definitions the advertised statements about `RelStore` use, besides `abs` (`Bridge.lean`)
and the spec (`RelSpec.lean`, `Rel.lean`). They are kept apart from the proofs
(`RelRefine.lean`) so that `Comparator/Challenge.lean` can import them.

* `boundarySet B`: the digests of a boundary, as the spec's finite set.
* `AcceptRelMeans c r`: what each result of `RelStore.accept` means, in the spec model.
-/

namespace Zrdt

open Crdt.Merkle

/-- The digests of a boundary, as a finite set (the spec's `B`). -/
def boundarySet (B : Boundary) : Finset Digest := B.keys.toFinset

open Examples in
example : hashRecord a1 ∈ boundarySet bnd := by
  simp [boundarySet, bnd]

/-- A digest is in `boundarySet B` exactly when it is a digest of `B`. -/
theorem mem_boundarySet {B : Boundary} {d : Digest} : d ∈ boundarySet B ↔ d ∈ B := by
  simp [boundarySet]

/-- The empty boundary gives the empty set. -/
@[simp] theorem boundarySet_empty : boundarySet ∅ = ∅ := by
  ext d; simp [mem_boundarySet]

/-- **What the result of `accept c r` means**, for the new store `c'`, relative to `c`'s boundary
`B` (with `B = ∅` these are the cases of `AcceptMeans`):

* `accepted d`: the spec store of `c'` is the spec's `acceptRel B` of `toSpec r`, `d` is the
  record's digest, every link of `r` is the digest of a stored record or a digest of `B`, the
  record is in the new store, and the boundary is the same.
* `missing ds`: nothing changed; `ds` is not empty, and it is exactly the links of `r` that are
  neither the digest of a stored record nor a digest of `B`.
* `collision d`: nothing changed; `d` is the digest of `r`, and the store holds a different
  record with that digest.
* `wrongChat`: nothing changed; `r` belongs to another chat.
* `tooLarge`: nothing changed; `r` has too many links, or it is new and the store is full. -/
def AcceptRelMeans (c : RelStore) (r : Rec) : AcceptResult × RelStore → Prop
  | (.accepted d, c') =>
    c'.raw.abs = acceptRel hashSpec (boundarySet c.boundary) c.raw.abs (toSpec r) ∧
      d = hashRecord r ∧
      (toSpec r).links ⊆ inView hashSpec c.raw.abs (boundarySet c.boundary) ∧
      toSpec r ∈ c'.raw.abs ∧ c'.boundary = c.boundary
  | (.missing ds, c') =>
    c' = c ∧ ds ≠ #[] ∧
      ∀ x, x ∈ ds ↔ x ∈ (toSpec r).links ∧ x ∉ inView hashSpec c.raw.abs (boundarySet c.boundary)
  | (.collision d, c') =>
    c' = c ∧ d = hashRecord r ∧ ∃ x ∈ c.raw.abs, hashSpec x = d ∧ x ≠ toSpec r
  | (.wrongChat, c') => c' = c ∧ r.group ≠ c.group
  | (.tooLarge, c') =>
    c' = c ∧ (¬ r.WellSized ∨ (hashRecord r ∉ digests hashSpec c.raw.abs ∧ maxRecords ≤ c.size + 1))

-- A `missing` result with an empty list means nothing.
example (c : RelStore) (r : Rec) : ¬ AcceptRelMeans c r (.missing #[], c) := by
  simp [AcceptRelMeans]

end Zrdt
