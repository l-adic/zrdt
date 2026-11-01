/-
Copyright (c) 2026 zrdt contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: zrdt contributors
-/
import Mathlib
import Crdt.Defs
import Crdt.Convergence
import Crdt.Liveness

set_option linter.unusedSectionVars false

/-!
# Hash-linked records: definitions

A replica stores a finite set of **records**. Each record names the records its author had
already seen, by their hashes (its **links**). Merging two replicas is set union, so every
phase 0 convergence result applies unchanged.

The hash function is a plain parameter `hash`. Nothing here assumes it is injective. Theorems
that need "different records have different hashes" instead conclude
`correct ∨ CollisionIn hash u`: either the result holds, or two different records inside `u`
have the same hash.

What a replica can check at run time: hash equality, and whether a record's links resolve to
records it holds. `Closed`, `heads`, `accept` and `digests` are all computable.
-/

namespace Crdt.Merkle

/-- A record: a payload, the hashes of the records its author had seen when writing it (its
links), and the author's name. The author is only a claim; `authorConfirmed` (`Chat.lean`)
says when it can be believed. -/
structure Record (α H K : Type*) where
  /-- The data the record carries. -/
  payload : α
  /-- Hashes of the records the author had seen (the author's heads at write time). -/
  links : Finset H
  /-- Who claims to have written the record. Nothing in this file checks it. -/
  author : K
deriving DecidableEq

/-- A store: a finite set of records. Merging two stores is set union. -/
abbrev Store (α H K : Type*) := Finset (Record α H K)

/-! ## A toy setting for the examples -/

namespace Toy

/-- Toy records: numbers as payloads and as hashes, one author. -/
abbrev R := Record ℕ ℕ Unit

/-- Toy hash: a record's hash is its payload. Records with equal payloads collide. -/
def hash (r : R) : ℕ := r.payload

/-- A record with no links. Hash `0`. -/
def r0 : R := ⟨0, ∅, ()⟩

/-- A record written after seeing `r0`. Hash `1`. -/
def r1 : R := ⟨1, {0}, ()⟩

/-- A different record that also has hash `0`, so it collides with `r0`. -/
def fake0 : R := ⟨0, {7}, ()⟩

end Toy

variable {α H K : Type*} [DecidableEq α] [DecidableEq H] [DecidableEq K]
variable (hash : Record α H K → H)

/-! ## Collisions -/

/-- Two different records in `u` have the same hash. This is the collision the integrity
theorems produce: it points to records the replicas actually hold. (A collision "somewhere"
always exists for a hash with a fixed output size, so it would make every theorem empty.) -/
def CollisionIn (u : Store α H K) : Prop := ∃ x ∈ u, ∃ y ∈ u, x ≠ y ∧ hash x = hash y

instance (u : Store α H K) : Decidable (CollisionIn hash u) := by
  unfold CollisionIn; infer_instance

example : CollisionIn Toy.hash {Toy.r0, Toy.fake0} := by decide
example : ¬ CollisionIn Toy.hash {Toy.r0, Toy.r1} := by decide

/-- Build a collision from two different records in `u` with the same hash. -/
theorem CollisionIn.of_mem {u : Store α H K} {x y : Record α H K} (hx : x ∈ u) (hy : y ∈ u)
    (hne : x ≠ y) (heq : hash x = hash y) : CollisionIn hash u :=
  ⟨x, hx, y, hy, hne, heq⟩

/-- A collision inside `u` is also inside any bigger store. -/
theorem CollisionIn.mono {u v : Store α H K} (huv : u ⊆ v) (h : CollisionIn hash u) :
    CollisionIn hash v := by
  obtain ⟨x, hx, y, hy, hne, heq⟩ := h
  exact ⟨x, huv hx, y, huv hy, hne, heq⟩

/-! ## Digests -/

/-- The hashes of the records in a store. -/
def digests (s : Store α H K) : Finset H := s.image hash

example : digests Toy.hash {Toy.r0, Toy.r1} = {0, 1} := by decide

theorem mem_digests {s : Store α H K} {d : H} : d ∈ digests hash s ↔ ∃ r ∈ s, hash r = d :=
  Finset.mem_image

/-- The hashes of a merged store are the hashes of both stores. -/
theorem digests_union (s t : Store α H K) :
    digests hash (s ∪ t) = digests hash s ∪ digests hash t :=
  Finset.image_union s t

/-- The empty store has no hashes. -/
theorem digests_empty : digests hash (∅ : Store α H K) = ∅ :=
  Finset.image_empty hash

/-! ## Closed stores -/

/-- Every link of every record in `s` is the hash of some record in `s`: if you hold a record,
you hold what it was built on. -/
def Closed (s : Store α H K) : Prop := ∀ r ∈ s, ∀ d ∈ r.links, ∃ r' ∈ s, hash r' = d

instance (s : Store α H K) : Decidable (Closed hash s) := by
  unfold Closed; infer_instance

example : Closed Toy.hash {Toy.r0, Toy.r1} := by decide
-- `r1` links hash `0`, but nothing in the store has hash `0`.
example : ¬ Closed Toy.hash {Toy.r1} := by decide

/-- The empty store is closed. -/
theorem closed_empty : Closed hash (∅ : Store α H K) := by
  simp [Closed]

/-- Merging two closed stores gives a closed store. -/
theorem closed_union {s t : Store α H K} (hs : Closed hash s) (ht : Closed hash t) :
    Closed hash (s ∪ t) := by
  intro r hr d hd
  rcases Finset.mem_union.mp hr with hr | hr
  · obtain ⟨r', hr', he⟩ := hs r hr d hd
    exact ⟨r', Finset.mem_union_left _ hr', he⟩
  · obtain ⟨r', hr', he⟩ := ht r hr d hd
    exact ⟨r', Finset.mem_union_right _ hr', he⟩

/-! ## Heads -/

/-- The heads of a store: hashes of the records in it that no record in it links to. These are
the latest records, and what a new record should link. -/
def heads (s : Store α H K) : Finset H :=
  (s.filter fun r ↦ ∀ r' ∈ s, hash r ∉ r'.links).image hash

example : heads Toy.hash {Toy.r0} = {0} := by decide
example : heads Toy.hash {Toy.r0, Toy.r1} = {1} := by decide

/-- `d` is a head of `s` when some record in `s` has hash `d` and no record in `s` links `d`. -/
theorem mem_heads {s : Store α H K} {d : H} :
    d ∈ heads hash s ↔ ∃ r ∈ s, hash r = d ∧ ∀ r' ∈ s, d ∉ r'.links := by
  simp only [heads, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨r, ⟨hr, hh⟩, rfl⟩
    exact ⟨r, hr, rfl, hh⟩
  · rintro ⟨r, hr, rfl, hh⟩
    exact ⟨r, ⟨hr, hh⟩, rfl⟩

/-- Every head is the hash of a record in the store. -/
theorem heads_subset_digests (s : Store α H K) : heads hash s ⊆ digests hash s :=
  Finset.image_subset_image (Finset.filter_subset _ _)

/-! ## Reachability and fetching -/

/-- `Reach hash s hs d`: starting from the hashes `hs` and following links of records in `s`,
you get to the hash `d`. -/
inductive Reach (s : Store α H K) (hs : Finset H) : H → Prop
  /-- Every starting hash is reached. -/
  | head {d : H} : d ∈ hs → Reach s hs d
  /-- If you reached a record of `s`, you reach each of its links. -/
  | link {r : Record α H K} {d : H} : r ∈ s → Reach s hs (hash r) → d ∈ r.links → Reach s hs d

example : Reach Toy.hash {Toy.r0, Toy.r1} {1} 0 :=
  .link (r := Toy.r1) (by decide) (.head (by decide)) (by decide)

/-- `s` holds a record for every hash you can reach from `hs`: nothing is missing. -/
def Complete (s : Store α H K) (hs : Finset H) : Prop :=
  ∀ d, Reach hash s hs d → ∃ r ∈ s, hash r = d

/-- Every record in `s` can be reached from `hs`: nothing extra was added. -/
def Tight (s : Store α H K) (hs : Finset H) : Prop := ∀ r ∈ s, Reach hash s hs (hash r)

/-- `s` is exactly what you get by fetching everything reachable from the heads `hs`. -/
def Fetched (s : Store α H K) (hs : Finset H) : Prop := Complete hash s hs ∧ Tight hash s hs

/-- A closed store whose starting hashes all resolve holds everything reachable from them.
Used to check `Complete` on examples. -/
theorem complete_of_closed {s : Store α H K} {hs : Finset H} (hc : Closed hash s)
    (hh : hs ⊆ digests hash s) : Complete hash s hs := by
  intro d hd
  cases hd with
  | head h => exact (mem_digests hash).mp (hh h)
  | link hr _ hl => exact hc _ hr _ hl

/-- Reachability is bounded by any set of hashes `R` that contains the start and contains the
links of every record of `s` whose hash is in `R`. Used to show a record is unreachable. -/
theorem Reach.mem_of_bound {s : Store α H K} {hs R : Finset H} (h0 : hs ⊆ R)
    (hstep : ∀ r ∈ s, hash r ∈ R → r.links ⊆ R) {d : H} (h : Reach hash s hs d) : d ∈ R := by
  induction h with
  | head hd => exact h0 hd
  | link hr _ hl ih => exact hstep _ hr ih hl

/-- Moving to a bigger store and new start hashes keeps reachability, as long as every old start
hash is still reachable. -/
theorem Reach.lift {s s' : Store α H K} {hs hs' : Finset H} (hss : s ⊆ s')
    (hh : ∀ d ∈ hs, Reach hash s' hs' d) {d : H} (h : Reach hash s hs d) :
    Reach hash s' hs' d := by
  induction h with
  | head hd => exact hh _ hd
  | link hr _ hl ih => exact .link (hss hr) ih hl

example : Complete Toy.hash {Toy.r0, Toy.r1} {1} := complete_of_closed _ (by decide) (by decide)

/-! ## Accepting one record -/

/-- Add `r` to `s` only if every link of `r` is the hash of a record already in `s`. This is
the run-time check. Otherwise `s` is unchanged. -/
def accept (s : Store α H K) (r : Record α H K) : Store α H K :=
  if r.links ⊆ digests hash s then insert r s else s

example : accept Toy.hash {Toy.r0} Toy.r1 = {Toy.r0, Toy.r1} := by decide
-- `r1` links hash `0`, which the empty store does not hold, so it is rejected.
example : accept Toy.hash ∅ Toy.r1 = ∅ := by decide

/-- The store a replica builds by accepting records one at a time, in list order. -/
def build (l : List (Record α H K)) : Store α H K := l.foldl (accept hash) ∅

example : build Toy.hash [Toy.r0, Toy.r1] = {Toy.r0, Toy.r1} := by decide
-- Order matters: `r1` arrives before what it links, so it is dropped.
example : build Toy.hash [Toy.r1, Toy.r0] = {Toy.r0} := by decide

/-- When the links resolve, accepting is inserting. -/
theorem accept_of_resolves {s : Store α H K} {r : Record α H K}
    (hl : r.links ⊆ digests hash s) : accept hash s r = insert r s := by
  simp [accept, hl]

/-- Accepting a record keeps a store closed. -/
theorem closed_accept {s : Store α H K} (hs : Closed hash s) (r : Record α H K) :
    Closed hash (accept hash s r) := by
  unfold accept
  split_ifs with hl
  · intro x hx d hd
    rcases Finset.mem_insert.mp hx with rfl | hx
    · obtain ⟨r', hr', he⟩ := (mem_digests hash).mp (hl hd)
      exact ⟨r', Finset.mem_insert_of_mem hr', he⟩
    · obtain ⟨r', hr', he⟩ := hs x hx d hd
      exact ⟨r', Finset.mem_insert_of_mem hr', he⟩
  · exact hs

/-- A store built by `accept` is closed. -/
theorem closed_build (l : List (Record α H K)) : Closed hash (build hash l) := by
  unfold build
  suffices ∀ s, Closed hash s → Closed hash (l.foldl (accept hash) s) from
    this ∅ (closed_empty hash)
  induction l with
  | nil => exact fun s hs ↦ hs
  | cons r l ih =>
    intro s hs
    rw [List.foldl_cons]
    exact ih _ (closed_accept hash hs r)

/-- Heads after adding a new record whose links resolve: the new record's hash, plus the old
heads it did not link. Or two records in the new store collide. -/
theorem heads_insert {s : Store α H K} {r : Record α H K} (hs : Closed hash s) (hr : r ∉ s)
    (hl : r.links ⊆ digests hash s) :
    heads hash (insert r s) = insert (hash r) (heads hash s \ r.links) ∨
      CollisionIn hash (insert r s) := by
  by_cases hc : CollisionIn hash (insert r s)
  · exact Or.inr hc
  left
  -- Nothing in the new store links `hash r`: a link to it would resolve, by closure, to a record
  -- of `s` with the same hash, which is a collision since `r ∉ s`.
  have hfresh : ∀ y ∈ insert r s, hash r ∉ y.links := by
    intro y hy hlink
    obtain ⟨z, hz, he⟩ : ∃ z ∈ s, hash z = hash r := by
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact (mem_digests hash).mp (hl hlink)
      · exact hs y hy _ hlink
    exact hc (CollisionIn.of_mem hash (Finset.mem_insert_of_mem hz) (Finset.mem_insert_self r s)
      (fun e ↦ hr (e ▸ hz)) he)
  ext d
  constructor
  · intro hd
    obtain ⟨x, hx, rfl, hh⟩ := (mem_heads hash).mp hd
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact Finset.mem_insert_self _ _
    · refine Finset.mem_insert_of_mem (Finset.mem_sdiff.mpr ⟨?_, ?_⟩)
      · exact (mem_heads hash).mpr ⟨x, hx, rfl, fun y hy ↦ hh y (Finset.mem_insert_of_mem hy)⟩
      · exact hh r (Finset.mem_insert_self r s)
  · intro hd
    rcases Finset.mem_insert.mp hd with rfl | hd
    · exact (mem_heads hash).mpr ⟨r, Finset.mem_insert_self r s, rfl, hfresh⟩
    · obtain ⟨hd, hnl⟩ := Finset.mem_sdiff.mp hd
      obtain ⟨x, hx, rfl, hh⟩ := (mem_heads hash).mp hd
      refine (mem_heads hash).mpr ⟨x, Finset.mem_insert_of_mem hx, rfl, fun y hy ↦ ?_⟩
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact hnl
      · exact hh y hy

/-! ## Convergence carries over from phase 0 -/

/-- Merging stores is set union. -/
theorem merge_eq_union (s t : Store α H K) : merge s t = s ∪ t :=
  rfl

/-- Strong eventual consistency for stores: replicas that received the same set of stores hold
the same store, in any order and with any repeats. -/
private theorem strong_eventual_consistency (l₁ l₂ : List (Store α H K))
    (h : l₁.toFinset = l₂.toFinset) : l₁.foldr merge ⊥ = l₂.foldr merge ⊥ :=
  Crdt.strong_eventual_consistency l₁ l₂ h

/-- Eventual agreement for stores under any fair delivery system. -/
private theorem eventual_agreement {ι : Type*} (sys : DeliverySystem ι (Store α H K)) (r₁ r₂ : ι) :
    ∃ T, ∀ t, T ≤ t → replicaState (sys.delivered r₁ t) = replicaState (sys.delivered r₂ t) :=
  sys.eventual_agreement r₁ r₂

end Crdt.Merkle
