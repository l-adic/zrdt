/-
Copyright (c) 2026 zrdt contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: zrdt contributors
-/
import Mathlib
import Crdt.Merkle.Defs
import Crdt.Merkle.Integrity

set_option linter.unusedSectionVars false

/-!
# A shared task list on hash-linked records

Each record either adds a task (by title) or removes one earlier add record (by its hash).
A title is on the list when some add record with that title has not been removed.

A remove counts only if it also links the record it removes. So a remove can only take away an
add its author had seen. A remove that does not link its target does nothing, however it got
into the store. This is what makes "add wins" hold for adds the remover had not seen.

The record's hash is its unique id, so there is no separate id allocator (phase 0's OR-Set
needed one as a hypothesis).
-/

namespace Crdt.Merkle.TaskList

/-- A task-list operation: add a task with a title, or remove the add record with hash
`target`. -/
inductive Op (H : Type*) where
  /-- Add a task with this title. -/
  | add (title : String)
  /-- Remove the add record whose hash is `target`. -/
  | remove (target : H)
deriving DecidableEq

variable {H K : Type*} [DecidableEq H] [DecidableEq K]

/-- The title an operation adds: `{title}` for an add, nothing for a remove. -/
private def Op.added : Op H → Finset String
  | .add title => {title}
  | .remove _ => ∅

example : (Op.add "buy milk" : Op ℕ).added = {"buy milk"} := rfl
example : (Op.remove 3 : Op ℕ).added = ∅ := rfl

variable (hash : Record (Op H) H K → H)

/-- `r` removes the record with hash `d`: it is a remove of `d`, and it links `d`. -/
def Removes (r : Record (Op H) H K) (d : H) : Prop := r.payload = .remove d ∧ d ∈ r.links

instance (r : Record (Op H) H K) (d : H) : Decidable (Removes r d) := by
  unfold Removes; infer_instance

example : Removes (⟨.remove 0, {0}, ()⟩ : Record (Op ℕ) ℕ Unit) 0 := by decide
-- A remove that does not link its target removes nothing.
example : ¬ Removes (⟨.remove 0, ∅, ()⟩ : Record (Op ℕ) ℕ Unit) 0 := by decide

/-- The titles on the list: titles of add records in `s` that no record in `s` removes. -/
def live (s : Store (Op H) H K) : Finset String :=
  (s.filter fun a ↦ ∀ r ∈ s, ¬ Removes r (hash a)).biUnion fun a ↦ a.payload.added

/-- A title is live when some add record with that title is in the store and no record in the
store removes it. -/
private theorem mem_live {s : Store (Op H) H K} {title : String} :
    title ∈ live hash s ↔ ∃ a ∈ s, a.payload = .add title ∧ ∀ r ∈ s, ¬ Removes r (hash a) := by
  simp only [live, Finset.mem_biUnion, Finset.mem_filter]
  constructor
  · rintro ⟨a, ⟨ha, hn⟩, ht⟩
    refine ⟨a, ha, ?_, hn⟩
    cases hp : a.payload with
    | add t => rw [hp] at ht; simp [Op.added] at ht; simp [ht]
    | remove _ => rw [hp] at ht; simp [Op.added] at ht
  · rintro ⟨a, ha, hp, hn⟩
    exact ⟨a, ⟨ha, hn⟩, by simp [hp, Op.added]⟩

/-! ## Same store, same list -/

/-- Equal stores show the same task list. -/
private theorem live_determined {s s' : Store (Op H) H K} (h : s = s') : live hash s = live hash s' :=
  congrArg (live hash) h

/-- Two replicas that fetched the same heads show the same task list. Or two records in their
stores have the same hash. -/
theorem fetched_live_agree {s s' : Store (Op H) H K} {hs : Finset H}
    (hS : Fetched hash s hs) (hT : Fetched hash s' hs) :
    live hash s = live hash s' ∨ CollisionIn hash (s ∪ s') :=
  (fetched_agree hash hS hT).imp (congrArg (live hash)) id

/-! ## Add wins -/

/-- An add record that nothing in `s` or `s'` removes is live after merging them. -/
private theorem add_survives_merge {s s' : Store (Op H) H K} {a : Record (Op H) H K} {title : String}
    (ha : a ∈ s) (hadd : a.payload = .add title) (h₁ : ∀ r ∈ s, ¬ Removes r (hash a))
    (h₂ : ∀ r ∈ s', ¬ Removes r (hash a)) : title ∈ live hash (merge s s') := by
  rw [merge_eq_union]
  refine (mem_live hash).mpr ⟨a, Finset.mem_union_left _ ha, hadd, fun r hr ↦ ?_⟩
  rcases Finset.mem_union.mp hr with hr | hr
  · exact h₁ r hr
  · exact h₂ r hr

/-- No record in a closed store removes a record that is not in it. Or two records collide once
the new record is added. -/
private theorem fresh_add_not_removed {s : Store (Op H) H K} {a : Record (Op H) H K}
    (hs : Closed hash s) (ha : a ∉ s) :
    (∀ r ∈ s, ¬ Removes r (hash a)) ∨ CollisionIn hash (insert a s) := by
  by_cases hc : CollisionIn hash (insert a s)
  · exact Or.inr hc
  left
  -- A remove of `hash a` links it, so by closure some record of `s` has that hash. It is not
  -- `a`, which is not in `s`: a collision.
  intro r hr hrm
  obtain ⟨z, hz, he⟩ := hs r hr _ hrm.2
  exact hc (CollisionIn.of_mem hash (Finset.mem_insert_of_mem hz) (Finset.mem_insert_self a s)
    (fun e ↦ ha (e ▸ hz)) he)

/-- **Add wins.** A replica adds a task (a new record `a`), while another replica, which has not
seen `a`, removes things. After merging, the task is live. Or two records in the merged store
collide. This covers the re-add case: a title removed on one replica and added again,
concurrently, on another stays on the list. -/
theorem add_wins {s s' : Store (Op H) H K} {a : Record (Op H) H K} {title : String}
    (hs : Closed hash s) (hs' : Closed hash s') (ha : a ∉ s) (ha' : a ∉ s')
    (hadd : a.payload = .add title) :
    title ∈ live hash (merge (insert a s) s') ∨ CollisionIn hash (merge (insert a s) s') := by
  rw [merge_eq_union, Finset.insert_union]
  have hnot : a ∉ s ∪ s' := by simp [ha, ha']
  refine (fresh_add_not_removed hash (closed_union hash hs hs') hnot).imp (fun h ↦ ?_) id
  refine (mem_live hash).mpr ⟨a, Finset.mem_insert_self _ _, hadd, fun r hr hrm ↦ ?_⟩
  rcases Finset.mem_insert.mp hr with rfl | hr
  · simp [Removes, hadd] at hrm
  · exact h r hr hrm

/-! ## Removes -/

/-- In a closed store, the target of every remove that counts is a record in the store. -/
theorem remove_requires_closure {s : Store (Op H) H K} {r : Record (Op H) H K} {d : H}
    (hs : Closed hash s) (hr : r ∈ s) (hrm : Removes r d) : ∃ a ∈ s, hash a = d :=
  hs r hr d hrm.2

/-- If a record in `s` removes `a`, a title stays live only through another add record, with a
different hash, that nothing removes. -/
private theorem remove_removes {s : Store (Op H) H K} {r a : Record (Op H) H K} {title : String}
    (hr : r ∈ s) (hrm : Removes r (hash a)) (ht : title ∈ live hash s) :
    ∃ a' ∈ s, a'.payload = .add title ∧ hash a' ≠ hash a ∧ ∀ r' ∈ s, ¬ Removes r' (hash a') := by
  obtain ⟨a', ha', hp, hn⟩ := (mem_live hash).mp ht
  exact ⟨a', ha', hp, fun he ↦ hn r hr (by rw [he]; exact hrm), hn⟩

/-- If a record in `s` removes `a`, and every add of `title` in `s` has the hash of `a`, then
`title` is not live. -/
theorem remove_removes_only {s : Store (Op H) H K} {r a : Record (Op H) H K} {title : String}
    (hr : r ∈ s) (hrm : Removes r (hash a))
    (honly : ∀ a' ∈ s, a'.payload = .add title → hash a' = hash a) : title ∉ live hash s := by
  intro ht
  obtain ⟨a', ha', hp, hne, -⟩ := remove_removes hash hr hrm ht
  exact hne (honly a' ha' hp)

/-! ## Scenario

Ann and Bob share a list. Ann adds "buy milk" (`rA`), Bob adds "call mom" (`rB`). Both see both.
Ann then removes "buy milk" (`rC`). Before Bob sees that, he adds "buy milk" again (`rD`).
Eve, who is not trusted, makes up records (`junk`, `bad`, `swapped`). -/

namespace Scenario

/-- Records of the scenario: numbers as hashes, names as authors. -/
private abbrev R := Record (Op ℕ) ℕ String

/-- Ann adds "buy milk". Hash `0`. -/
private def rA : R := ⟨.add "buy milk", ∅, "ann"⟩
/-- Bob adds "call mom". Hash `1`. -/
private def rB : R := ⟨.add "call mom", ∅, "bob"⟩
/-- Ann, having seen `rA` and `rB`, removes `rA`. Hash `2`. -/
private def rC : R := ⟨.remove 0, {0, 1}, "ann"⟩
/-- Bob, having seen `rA` and `rB` but not `rC`, adds "buy milk" again. Hash `3`. -/
private def rD : R := ⟨.add "buy milk", {0, 1}, "bob"⟩
/-- A record Eve made up and slipped into a store she served. Hash `4`. -/
private def junk : R := ⟨.add "free money", ∅, "eve"⟩
/-- A remove of `rA` by Eve that does not link `rA`. Hash `5`. -/
private def bad : R := ⟨.remove 0, ∅, "eve"⟩
/-- What Eve serves in place of `rA`. Not in the hash table, so its hash is `6`. -/
private def swapped : R := ⟨.add "buy beer", ∅, "ann"⟩

/-- The records with known hashes, in hash order. -/
private def table : List R := [rA, rB, rC, rD, junk, bad]

/-- Toy hash: a record's position in `table`. Every record not in the table gets `6`, so this
hash has collisions, but none among the records of the scenario stores. -/
private def toyHash (r : R) : ℕ := table.idxOf r

example : toyHash rA = 0 ∧ toyHash rB = 1 ∧ toyHash rC = 2 ∧ toyHash rD = 3 := by decide

-- The toy hash collides outside the table. This is why the theorems use `CollisionIn`.
example : Collision toyHash := ⟨⟨.add "x", ∅, ""⟩, ⟨.add "y", ∅, ""⟩, by decide, by decide⟩

/-- Another record not in the table. It has hash `6`, like `swapped`. -/
private def stray : R := ⟨.add "buy bread", ∅, "eve"⟩

-- Stores with the same hashes are the same store.
example : ({rA, rB} : Store (Op ℕ) ℕ String) = {rB, rA} :=
  (eq_of_digests_eq toyHash (by decide)).resolve_right (by decide)

-- The collision case does happen: `{swapped}` and `{stray}` have the same hashes but are
-- different stores, and their two records collide.
example : digests toyHash {swapped} = digests toyHash {stray} ∧
    ({swapped} : Store (Op ℕ) ℕ String) ≠ {stray} ∧ CollisionIn toyHash {swapped, stray} := by
  decide

-- Same hash, different records: `accept_unique` can only report the collision.
example : CollisionIn toyHash {swapped, stray} :=
  (accept_unique toyHash (d := 6) (by decide) (by decide)).resolve_left (by decide)

/-- Ann's store after her remove. -/
private def ann : Store (Op ℕ) ℕ String := {rA, rB, rC}
/-- Bob's store before his re-add. -/
private def bob : Store (Op ℕ) ℕ String := {rA, rB}

-- Structure: closed, and the heads move from `{hA, hB}` to `{hC}`.
example : Closed toyHash ann := by decide
example : heads toyHash bob = {0, 1} := by decide
example : heads toyHash ann = {2} := by decide

-- The list Ann sees, built in two different orders.
example : live toyHash ann = {"call mom"} := by decide
#guard live toyHash (insert rC (insert rB (insert rA ∅))) = {"call mom"}
#guard live toyHash (insert rA (insert rC (insert rB ∅))) = {"call mom"}

-- Building by `accept` depends on arrival order: `rC` arriving before `rA` is dropped.
example : build toyHash [rA, rB, rC] = ann := by decide
example : build toyHash [rC, rA, rB] = bob := by decide

-- Ann's remove links both heads of Bob's store, so it becomes the only head.
example : heads toyHash (insert rC bob) = {toyHash rC} :=
  (heads_insert_of_links_heads toyHash (by decide) (by decide) (by decide)).resolve_right
    (by decide)

-- `junk` links nothing, so the old heads stay and its hash joins them.
example :
    heads toyHash (insert junk bob) = insert (toyHash junk) (heads toyHash bob \ junk.links) :=
  (heads_insert toyHash (by decide) (by decide) (by decide)).resolve_right (by decide)

-- The receipt for offering `rC` to Bob lists `rC` as a head.
example : (receipt toyHash bob rC).digest ∈ (receipt toyHash bob rC).heads :=
  (receipt_confirms toyHash (by decide) (by decide) (by decide)).resolve_right (by decide)

/-- Ann's records accepted in her order are fetched from hash `2`: `fetched_build`, with no
collision inside. -/
private theorem annOrder_fetched : Fetched toyHash (build toyHash [rA, rB, rC]) {2} := by
  have h := (fetched_build toyHash [rA, rB, rC]).resolve_right (by decide)
  rwa [show heads toyHash (build toyHash [rA, rB, rC]) = {2} by decide] at h

/-- The same records accepted in another order are also fetched from hash `2`. -/
private theorem otherOrder_fetched : Fetched toyHash (build toyHash [rB, rA, rC]) {2} := by
  have h := (fetched_build toyHash [rB, rA, rC]).resolve_right (by decide)
  rwa [show heads toyHash (build toyHash [rB, rA, rC]) = {2} by decide] at h

/-- Ann's store is fetched from its heads. -/
private theorem ann_fetched : Fetched toyHash ann {2} := by
  rw [show ann = build toyHash [rA, rB, rC] by decide]
  exact annOrder_fetched

-- The headline, applied: both orders are fetched from `{2}`, so they give the same store.
example : build toyHash [rA, rB, rC] = build toyHash [rB, rA, rC] :=
  (fetched_agree toyHash annOrder_fetched otherOrder_fetched).resolve_right (by decide)

-- They still agree after merging in Bob's re-add, and they show the same task list.
example : merge {rD} (build toyHash [rA, rB, rC]) = merge {rD} (build toyHash [rB, rA, rC]) :=
  (merge_fetched toyHash {rD} annOrder_fetched otherOrder_fetched).resolve_right (by decide)

example :
    live toyHash (build toyHash [rA, rB, rC]) = live toyHash (build toyHash [rB, rA, rC]) :=
  (fetched_live_agree toyHash annOrder_fetched otherOrder_fetched).resolve_right (by decide)

-- Eve adds `junk` to what she serves: the store is not fetched from `{2}`, since `junk` cannot be
-- reached from hash `2`.
example : ¬ Tight toyHash (insert junk ann) {2} := by
  intro h
  have := (h junk (by decide)).mem_of_bound toyHash (R := {0, 1, 2}) (by decide) (by decide)
  exact absurd this (by decide)

-- Eve swaps `rA` for `swapped`: the store is missing the record with hash `0`.
example : ¬ Complete toyHash {swapped, rB, rC} {2} := by
  intro h
  have := h 0 (.link (r := rC) (by decide) (.head (by decide)) (by decide))
  exact absurd this (by decide)

-- `Tight` is needed: both stores hold everything reachable from `{2}`, they differ, and no two
-- of their records collide.
example : Complete toyHash ann {2} ∧ Complete toyHash (insert junk ann) {2} ∧
    ann ≠ insert junk ann ∧ ¬ CollisionIn toyHash (ann ∪ insert junk ann) :=
  ⟨complete_of_closed toyHash (by decide) (by decide),
    complete_of_closed toyHash (by decide) (by decide), by decide, by decide⟩

-- Add wins, applied: Bob's re-add `rD` survives merging with Ann's remove.
example : "buy milk" ∈ live toyHash (merge (insert rD bob) ann) :=
  (add_wins toyHash (by decide) (by decide) (by decide) (by decide) rfl).resolve_right (by decide)

example : live toyHash (merge (insert rD bob) ann) = {"buy milk", "call mom"} := by decide

-- Ann's remove counts, and its target is in her store.
example : ∃ a ∈ ann, toyHash a = 0 := remove_requires_closure toyHash (r := rC) (by decide)
  (by decide) (by decide)

-- Ann's remove takes "buy milk" off her list: `rA` was the only add of it.
example : "buy milk" ∉ live toyHash ann :=
  remove_removes_only toyHash (r := rC) (a := rA) (by decide) (by decide) (by decide)

-- The list rejects a wrong answer.
example : live toyHash ann ≠ {"buy milk", "call mom"} := by decide

-- Eve's `bad` remove does not link `rA`, so it removes nothing.
example : live toyHash {rA, rB, bad} = {"buy milk", "call mom"} := by decide

end Scenario

end Crdt.Merkle.TaskList
