/-
Copyright (c) 2026 zrdt contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: zrdt contributors
-/
import Mathlib
import Crdt.Merkle.Defs
import Crdt.Merkle.Integrity
import Crdt.Merkle.Chat
import Zrdt.Store

set_option linter.unusedSectionVars false

/-!
# From the shipped store to the spec model (docs/PLAN.md §3.2, phase B)

The shipped code (`Zrdt`, no Mathlib) stores records in a map from digest to record. The spec
(`Crdt.Merkle`) talks about a finite set of records and a hash function. This file connects them.

* `Digest` gets a `LinearOrder`: the same byte-by-byte order the code uses (`compare`).
* `toSpec r` is the spec record of a shipped record: payload `(group, commit)`, the links as a
  finite set, and the author.
* `hashSpec` is the spec's hash function. It is the shipped digest: `hashSpec (toSpec r) =
  hashRecord r` (`hashSpec_toSpec`).
* `RawStore.abs c` (and `abs` for a `CheckedStore`) is the set of the spec records of the stored
  records.

**The bridge.** If a raw store is correct (`Built`), then in the spec model:

* `Built.acceptBuilt`: its records can be accepted one at a time from the empty store
  (`AcceptBuilt`);
* `Built.mem_heads_iff`: its head cache holds exactly the spec's heads;
* `Built.no_collision`: no two of its records have the same digest;
* `Built.closed`-style: every link is the digest of a stored record (`Built.closed_abs`).

The advertised statements built on these are in `Crdt/Merkle/Api.lean`.
-/

namespace Zrdt

open Crdt.Merkle

/-! ## The order on digests -/

/-- A digest compares equal to itself. -/
theorem Digest.compare_self (a : Digest) : compare a a = .eq :=
  Std.ReflCmp.compare_self (cmp := (compare : Digest → Digest → Ordering))

/-- Swapping the arguments of `compare` swaps the result. -/
theorem Digest.compare_swap (a b : Digest) : compare b a = (compare a b).swap :=
  Std.OrientedCmp.eq_swap (cmp := (compare : Digest → Digest → Ordering))

/-- Digests that compare equal are equal. -/
theorem Digest.eq_of_compare {a b : Digest} (h : compare a b = .eq) : a = b :=
  Std.LawfulEqCmp.eq_of_compare (cmp := (compare : Digest → Digest → Ordering)) h

/-- Digests are linearly ordered byte by byte. This is the order the shipped code uses
(`compare`), so `a < b` exactly when `compare a b = .lt` (`Digest.lt_iff_compare`). -/
instance Digest.instLinearOrder : LinearOrder Digest where
  le a b := compare a b ≠ .gt
  lt a b := compare a b = .lt
  le_refl a := by
    show compare a a ≠ .gt
    rw [Digest.compare_self]; decide
  le_trans a b c h₁ h₂ :=
    Std.TransCmp.le_trans (cmp := (compare : Digest → Digest → Ordering)) h₁ h₂
  lt_iff_le_not_ge a b := by
    show compare a b = .lt ↔ compare a b ≠ .gt ∧ ¬ compare b a ≠ .gt
    rw [Digest.compare_swap a b]
    cases compare a b <;> decide
  le_antisymm a b h₁ h₂ := by
    change compare a b ≠ .gt at h₁
    change compare b a ≠ .gt at h₂
    rw [Digest.compare_swap a b] at h₂
    apply Digest.eq_of_compare
    cases h : compare a b <;> simp_all
  le_total a b := by
    show compare a b ≠ .gt ∨ compare b a ≠ .gt
    rw [Digest.compare_swap a b]
    cases compare a b <;> decide
  toDecidableLE a b := inferInstanceAs (Decidable (compare a b ≠ .gt))
  toDecidableEq := inferInstance
  toDecidableLT a b := inferInstanceAs (Decidable (compare a b = .lt))
  compare a b := compare a b
  compare_eq_compareOfLessAndEq a b := by
    show compare a b = if compare a b = .lt then .lt else if a = b then .eq else .gt
    cases h : compare a b
    · simp
    · simp [Digest.eq_of_compare h]
    · have hne : a ≠ b := by
        rintro rfl; rw [Digest.compare_self] at h; cases h
      simp [hne]

/-- `<` on digests is the code's `compare a b = .lt`. -/
theorem Digest.lt_iff_compare {a b : Digest} : a < b ↔ compare a b = .lt := Iff.rfl

example : Examples.dig 1 < Examples.dig 2 := by decide +kernel

/-! ## Spec records -/

/-- The payload of a spec record: the chat and the commitment. -/
abbrev Payload := GroupId × Digest

/-- A spec record over shipped types: payload `(group, commit)`, digest links, an author. -/
abbrev SpecRec := Record Payload Digest Aci

/-- A spec store over shipped types: a finite set of spec records. -/
abbrev SpecStore := Store Payload Digest Aci

/-- The spec record of a shipped record: the same group, commit and author, and its links as a
finite set. -/
def toSpec (r : Rec) : SpecRec := ⟨(r.group, r.commit), r.links.toList.toFinset, r.author⟩

example : (toSpec Examples.first).links = ∅ := rfl

/-- The links of a spec record in increasing order, with no repeats. -/
theorem sort_links_strictlySorted (x : SpecRec) :
    StrictlySorted (x.links.sort (fun a b : Digest => a ≤ b)).toArray := by
  show (x.links.sort (fun a b : Digest => a ≤ b)).toArray.toList.Pairwise _
  rw [List.toList_toArray]
  exact ((Finset.pairwise_sort x.links (fun a b : Digest => a ≤ b)).and
    (Finset.sort_nodup x.links (fun a b : Digest => a ≤ b))).imp fun h => lt_of_le_of_ne h.1 h.2

/-- The shipped record of a spec record: the links are put in increasing order. This undoes
`toSpec` (`ofSpec_toSpec`). -/
def ofSpec (x : SpecRec) : Rec :=
  ⟨x.payload.1, x.payload.2, (x.links.sort (fun a b : Digest => a ≤ b)).toArray, x.author,
    sort_links_strictlySorted x⟩

/-- Turning a shipped record into a spec record and back gives the same record: a record's
links are already in increasing order. -/
@[simp] theorem ofSpec_toSpec (r : Rec) : ofSpec (toSpec r) = r := by
  have hp : r.links.toList.Pairwise (· < ·) := r.links_sorted
  have hnd : r.links.toList.Nodup := hp.imp ne_of_lt
  have hs : r.links.toList.toFinset.sort (fun a b : Digest => a ≤ b) = r.links.toList :=
    (List.toFinset_sort _ hnd).mpr (hp.imp le_of_lt)
  ext1
  · rfl
  · rfl
  · show (r.links.toList.toFinset.sort (fun a b : Digest => a ≤ b)).toArray = r.links
    rw [hs, Array.toArray_toList]
  · rfl

/-- Different shipped records have different spec records. -/
theorem toSpec_injective : Function.Injective toSpec := fun r s h => by
  rw [← ofSpec_toSpec r, h, ofSpec_toSpec]

/-- The spec's hash function: the shipped digest of the record (`hashSpec_toSpec`). -/
def hashSpec (x : SpecRec) : Digest := hashRecord (ofSpec x)

/-- **The spec hash is the shipped digest.** -/
@[simp] theorem hashSpec_toSpec (r : Rec) : hashSpec (toSpec r) = hashRecord r := by
  simp [hashSpec]

example : hashSpec (toSpec Examples.first) = hashRecord Examples.first := hashSpec_toSpec _

/-! ## The spec store of a shipped store -/

/-- The spec store of a raw store: the spec records of its stored records. -/
def RawStore.abs (c : RawStore) : SpecStore := (c.map.toList.map fun p => toSpec p.2).toFinset

/-- The spec store of a checked store (docs/PLAN.md §3.2 writes `abs c`). -/
def abs (c : CheckedStore) : SpecStore := c.raw.abs

example : abs (CheckedStore.empty Examples.group) = ∅ := by
  simp [abs, RawStore.abs, CheckedStore.empty]

/-- A spec record is in `abs` exactly when it is the spec record of a stored record. -/
theorem RawStore.mem_abs {c : RawStore} {x : SpecRec} :
    x ∈ c.abs ↔ ∃ (k : Digest) (r : Rec), c.map[k]? = some r ∧ toSpec r = x := by
  simp only [RawStore.abs, List.mem_toFinset, List.mem_map]
  constructor
  · rintro ⟨⟨k, r⟩, hk, rfl⟩
    exact ⟨k, r, Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some.mp hk, rfl⟩
  · rintro ⟨k, r, hk, rfl⟩
    exact ⟨(k, r), Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some.mpr hk, rfl⟩

/-- `abs` of a checked store, by membership. -/
theorem mem_abs {c : CheckedStore} {x : SpecRec} :
    x ∈ abs c ↔ ∃ (k : Digest) (r : Rec), c.raw.map[k]? = some r ∧ toSpec r = x :=
  RawStore.mem_abs

/-! ## Accept orders give accept-built stores -/

/-- Accepting the records of an accept order oldest first, in the spec model, accepts every one
of them. -/
theorem AcceptOrder.build_eq {l : List Rec} (h : AcceptOrder l) :
    build hashSpec (l.reverse.map toSpec) = (l.map toSpec).toFinset := by
  induction h with
  | nil => rfl
  | @cons r older hr _ ih =>
    show List.foldl (accept hashSpec) ∅ ((r :: older).reverse.map toSpec) = _
    rw [List.reverse_cons, List.map_append, List.foldl_append]
    change List.foldl (accept hashSpec) (build hashSpec (older.reverse.map toSpec)) _ = _
    rw [ih, List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil, List.map_cons,
      List.toFinset_cons]
    apply accept_of_resolves
    intro d hd
    have hd' : d ∈ r.links := by simpa [toSpec] using hd
    obtain ⟨r', hr', rfl⟩ := hr d hd'
    exact (mem_digests hashSpec).mpr
      ⟨toSpec r', List.mem_toFinset.mpr (List.mem_map_of_mem hr'), hashSpec_toSpec r'⟩

/-- The spec records of an accept order form an accept-built store. -/
theorem AcceptOrder.acceptBuilt {l : List Rec} (h : AcceptOrder l) :
    AcceptBuilt hashSpec (l.map toSpec).toFinset :=
  ⟨l.reverse.map toSpec, by ext x; simp, h.build_eq⟩

/-! ## The bridge from `Built` -/

namespace Built

variable {c : RawStore}

/-- In a correct store, a digest is stored exactly when some spec record of the store has it as
its spec hash. -/
theorem mem_digests_abs (h : Built c) {d : Digest} :
    d ∈ digests hashSpec c.abs ↔ d ∈ c.map := by
  rw [mem_digests, Std.ExtTreeMap.mem_iff_isSome_getElem?, Option.isSome_iff_exists]
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨k, r, hk, rfl⟩ := RawStore.mem_abs.mp hx
    rw [hashSpec_toSpec, h.hash_eq k r hk]
    exact ⟨r, hk⟩
  · rintro ⟨r, hr⟩
    exact ⟨toSpec r, RawStore.mem_abs.mpr ⟨d, r, hr, rfl⟩, by rw [hashSpec_toSpec, h.hash_eq d r hr]⟩

/-- **A correct store is accept-built** in the spec model. -/
theorem acceptBuilt (h : Built c) : AcceptBuilt hashSpec c.abs := by
  obtain ⟨l, hl, hmem⟩ := h.order
  have : c.abs = (l.map toSpec).toFinset := by
    ext x
    rw [RawStore.mem_abs, List.mem_toFinset, List.mem_map]
    constructor
    · rintro ⟨k, r, hk, rfl⟩
      exact ⟨r, (hmem r).mpr ⟨k, hk⟩, rfl⟩
    · rintro ⟨r, hr, rfl⟩
      obtain ⟨k, hk⟩ := (hmem r).mp hr
      exact ⟨k, r, hk, rfl⟩
  rw [this]
  exact hl.acceptBuilt

/-- **No collision in a correct store**: two different stored records never have the same
digest, since each is stored under its own digest. -/
theorem no_collision (h : Built c) : ¬ CollisionIn hashSpec c.abs := by
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

/-- **The head cache is right**: a digest is in the cache exactly when it is a head of the spec
store. -/
theorem mem_heads_iff (h : Built c) {d : Digest} : d ∈ c.heads ↔ d ∈ heads hashSpec c.abs := by
  rw [h.heads_iff, mem_heads]
  constructor
  · rintro ⟨hd, hnl⟩
    obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp (Std.ExtTreeMap.mem_iff_isSome_getElem?.mp hd)
    refine ⟨toSpec r, RawStore.mem_abs.mpr ⟨d, r, hr, rfl⟩, by rw [hashSpec_toSpec,
      h.hash_eq d r hr], fun y hy hdy => ?_⟩
    obtain ⟨k, r', hk, rfl⟩ := RawStore.mem_abs.mp hy
    exact hnl k r' hk (by simpa [toSpec] using hdy)
  · rintro ⟨x, hx, rfl, hnl⟩
    obtain ⟨k, r, hk, rfl⟩ := RawStore.mem_abs.mp hx
    refine ⟨?_, fun k' r' hk' hl => hnl (toSpec r') (RawStore.mem_abs.mpr ⟨k', r', hk', rfl⟩)
      (by simpa [toSpec] using hl)⟩
    rw [hashSpec_toSpec, h.hash_eq k r hk]
    exact Std.ExtTreeMap.mem_iff_isSome_getElem?.mpr (by simp [hk])

/-- **The spec store is closed**: every link of a stored record is the digest of a stored
record. -/
theorem closed_abs (h : Built c) : Closed hashSpec c.abs := by
  intro x hx d hd
  obtain ⟨k, r, hk, rfl⟩ := RawStore.mem_abs.mp hx
  have hd' : d ∈ r.links := by simpa [toSpec] using hd
  exact (mem_digests hashSpec).mp ((h.mem_digests_abs).mpr (h.closed k r hk d hd'))

end Built

end Zrdt
