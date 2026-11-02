/-
Copyright (c) 2026 zrdt contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: zrdt contributors
-/
import Mathlib
import Crdt.Merkle.Bridge
import Crdt.Merkle.EncodeProofs
import Zrdt.Git

/-!
# The apps, lane git: proofs with Mathlib (docs/apps/BUILD_M1.md §C.3)

**Owner: lane git.** Proofs about git that need the spec model (`abs`). Statements for which Init
and Std suffice live in `core/Zrdt/Git.lean`. `Crdt/Merkle/Api.lean` imports this file and states
lane git's advertised statements in its section `[lane git]` (`refs_agree` and `force_visible`
need `CheckedStore.agree`, a statement of `Api.lean`), so this file does not import `Api.lean`.

`refs_agree` goes through three steps (BUILD_M1 §C.3):
1. `CheckedStore.agree` gives equal record sets (`abs c = abs d`), or a collision of record
   digests, which `sha256Collision_of` turns into a SHA-256 collision (`encode_injective`);
2. equal record sets are equal maps (`map_eq_of_abs_eq`: each record is stored under its own
   digest);
3. on equal maps, `Git.gitView_congr` (core) gives equal views, or two different held openings of
   one record, a SHA-256 collision (`Git.opening_unique`).
-/

namespace Zrdt.Git

open Crdt.Merkle

/-- Two checked stores that hold the same records (in the spec model) hold them under the same
digests: every record is stored under its own digest (`Built.hash_eq`). -/
theorem map_eq_of_abs_eq {c d : CheckedStore} (h : abs c = abs d) : c.raw.map = d.raw.map := by
  have key : ∀ {c d : CheckedStore}, abs c = abs d →
      ∀ (k : Digest) (r : Rec), c.raw.map[k]? = some r → d.raw.map[k]? = some r := by
    intro c d h k r hk
    have hx : toSpec r ∈ abs d := h ▸ mem_abs.mpr ⟨k, r, hk, rfl⟩
    obtain ⟨k', r', hk', he⟩ := mem_abs.mp hx
    obtain rfl : r' = r := toSpec_injective he
    have h1 := c.built.hash_eq k r' hk
    have h2 := d.built.hash_eq k' r' hk'
    rw [← h1, h2]
    exact hk'
  apply Std.ExtTreeMap.ext_getElem?
  intro k
  cases hc : c.raw.map[k]? with
  | some r => exact (key h k r hc).symm
  | none =>
    cases hd : d.raw.map[k]? with
    | none => rfl
    | some r =>
      have := key h.symm k r hd
      rw [hc] at this
      cases this

/-- A record in `abs c ∪ abs d` is the spec record of a stored record. -/
theorem exists_rec_of_mem {c d : CheckedStore} {x : SpecRec} (hx : x ∈ abs c ∪ abs d) :
    ∃ r : Rec, toSpec r = x := by
  rcases Finset.mem_union.mp hx with hx | hx
  · obtain ⟨_, r, _, rfl⟩ := mem_abs.mp hx
    exact ⟨r, rfl⟩
  · obtain ⟨_, r, _, rfl⟩ := mem_abs.mp hx
    exact ⟨r, rfl⟩

/-- **A record-digest collision across two stores is a SHA-256 collision**: two different records
with one digest have two different encodings with one SHA-256 (`encode_injective`). -/
theorem sha256Collision_of {c d : CheckedStore} (h : CollisionIn hashSpec (abs c ∪ abs d)) :
    ∃ x y : ByteArray, x ≠ y ∧ sha256 x = sha256 y := by
  obtain ⟨x, hx, y, hy, hne, hxy⟩ := h
  obtain ⟨r, rfl⟩ := exists_rec_of_mem hx
  obtain ⟨r', rfl⟩ := exists_rec_of_mem hy
  rw [hashSpec_toSpec, hashSpec_toSpec] at hxy
  have hne' : r ≠ r' := fun he => hne (he ▸ rfl)
  exact ⟨_, _, (hashRecord_collision hne' hxy).1, (hashRecord_collision hne' hxy).2⟩

/-- Equal record sets, complete openings on both sides: equal views, or a SHA-256 collision. -/
theorem gitView_agree_of_abs {c d : CheckedStore} {hc hd : Array (Digest × ByteArray)}
    (repo : String) (h : abs c = abs d) (hcc : Complete c hc) (hdc : Complete d hd) :
    gitView (tableOfStore c hc) repo = gitView (tableOfStore d hd) repo ∨
      ∃ x y : ByteArray, x ≠ y ∧ sha256 x = sha256 y :=
  gitView_congr repo (map_eq_of_abs_eq h) hcc hdc

end Zrdt.Git
