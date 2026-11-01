/-
Copyright (c) 2026 zrdt contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: zrdt contributors
-/
import Mathlib
import Crdt.Merkle.Bridge

set_option linter.unusedSectionVars false

/-!
# What the shipped store guarantees (docs/PLAN.md §3.2)

These are the advertised statements about the shipped code, `Zrdt.CheckedStore`. Each one is
about `abs c`, the set of records the store holds, seen in the spec model (`Bridge.lean`), with
`hashSpec` as the hash: the record digest the code computes.

Part 1 (this file so far):

* `CheckedStore.no_collision`: no two different records in a store have the same digest.
* `CheckedStore.fetched`: a store holds everything its heads reach, and nothing else.
* `CheckedStore.agree`: two stores with the same heads hold the same records, or two records
  across the two stores have the same digest (a SHA-256 collision).

TODO (later lanes): `abs_accept`, `abs_merge`, `open_iff`, `salvage_spec`, `encode_open`,
`confirmed`, `classify_spec`, `encode_injective`.
-/

namespace Zrdt

open Crdt.Merkle

/-- **No collision in a store.** Two different records in a checked store never have the same
digest: each record is stored under its own digest. -/
theorem CheckedStore.no_collision (c : CheckedStore) : ¬ CollisionIn hashSpec (abs c) :=
  c.built.no_collision

/-- **A store is fetched from its heads.** Following links from the store's heads reaches only
records the store holds, and reaches every record it holds. There is no collision disjunct:
the store has no collision (`no_collision`). -/
theorem CheckedStore.fetched (c : CheckedStore) :
    Fetched hashSpec (abs c) (Crdt.Merkle.heads hashSpec (abs c)) :=
  (fetched_build hashSpec c.acceptBuilt).resolve_right c.no_collision

/-- **Same heads, same store.** Two checked stores whose heads are equal (as sets of digests)
hold the same records. Or two different records, across the two stores, have the same digest.
This is what lets two members compare their histories by comparing heads only. -/
theorem CheckedStore.agree (c d : CheckedStore) (h : c.heads = d.heads) :
    abs c = abs d ∨ CollisionIn hashSpec (abs c ∪ abs d) := by
  have hh : Crdt.Merkle.heads hashSpec (abs c) = Crdt.Merkle.heads hashSpec (abs d) := by
    ext x
    rw [← c.mem_heads_iff, ← d.mem_heads_iff, h]
  exact fetched_agree hashSpec c.fetched (hh ▸ d.fetched)

/-! ## Examples

Each statement on a concrete store, with every hypothesis discharged. -/

example : ¬ CollisionIn hashSpec (abs Examples.all4) := Examples.all4.no_collision

example : Fetched hashSpec (abs Examples.all4) (Crdt.Merkle.heads hashSpec (abs Examples.all4)) :=
  Examples.all4.fetched

example : abs Examples.storeAB = abs Examples.storeAB ∨
    CollisionIn hashSpec (abs Examples.storeAB ∪ abs Examples.storeAB) :=
  Examples.storeAB.agree Examples.storeAB rfl

/-! ## The statements reject bad stores

A store that holds a reply but not the message it links is not fetched from its heads: the link
leads to nothing. (A checked store can never look like this, by `fetched`.) And two stores that
hold different records, with no collision, fail the conclusion of `agree`: so `agree` really
says that equal heads force equal stores. -/

/-- A record whose only link is the digest `dig 1`, which no record has. -/
def Examples.orphan : Rec := Rec.make Examples.group (Examples.dig 0xb1) #[Examples.dig 1]
  Examples.alice

/-- The orphan's digest is not `dig 1` (computed by the kernel). -/
theorem Examples.orphan_hash_ne : hashRecord Examples.orphan ≠ Examples.dig 1 := by
  decide +kernel

example : ¬ Fetched hashSpec {toSpec Examples.orphan}
    (Crdt.Merkle.heads hashSpec {toSpec Examples.orphan}) := by
  intro h
  have hhead : hashRecord Examples.orphan ∈
      Crdt.Merkle.heads hashSpec {toSpec Examples.orphan} := by
    refine (mem_heads hashSpec).mpr ⟨toSpec Examples.orphan, Finset.mem_singleton_self _,
      hashSpec_toSpec _, fun y hy hl => ?_⟩
    rw [Finset.mem_singleton] at hy
    subst hy
    simp [Examples.orphan] at hl
    exact Examples.orphan_hash_ne hl
  obtain ⟨x, hx, he⟩ := h.1 (Examples.dig 1) (.link (Finset.mem_singleton_self _)
    (by rw [hashSpec_toSpec]; exact .head hhead) (by simp [Examples.orphan]))
  rw [Finset.mem_singleton] at hx
  subst hx
  rw [hashSpec_toSpec] at he
  exact Examples.orphan_hash_ne he

/-- `first` and `a1` have different digests (computed by the kernel). -/
theorem Examples.first_hash_ne_a1 : hashRecord Examples.first ≠ hashRecord Examples.a1 := by
  decide +kernel

example : ¬ (({toSpec Examples.first} : SpecStore) = {toSpec Examples.a1} ∨
    CollisionIn hashSpec ({toSpec Examples.first} ∪ {toSpec Examples.a1})) := by
  rintro (h | ⟨x, hx, y, hy, hne, he⟩)
  · have : toSpec Examples.first = toSpec Examples.a1 := Finset.singleton_inj.mp h
    have := congrArg Rec.commit (toSpec_injective this)
    simp [Examples.first, Examples.a1] at this
    exact absurd (congrArg (fun d : Digest => d.bytes.data[0]!) this) (by decide)
  · simp only [Finset.mem_union, Finset.mem_singleton] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact hne rfl
    · exact Examples.first_hash_ne_a1 (by simpa using he)
    · exact Examples.first_hash_ne_a1 (by simpa using he.symm)
    · exact hne rfl

end Zrdt
