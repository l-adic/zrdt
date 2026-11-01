/-
Copyright (c) 2026 zrdt contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: zrdt contributors
-/
import Mathlib
import Crdt.Merkle.Bridge
import Crdt.Merkle.Refine
import Crdt.Merkle.ClassifyFast

set_option linter.unusedSectionVars false

/-!
# What the shipped store guarantees (docs/PLAN.md §3.2)

These are the advertised statements about the shipped code, `Zrdt.CheckedStore`. Each one is
about `abs c`, the set of records the store holds, seen in the spec model (`Bridge.lean`), with
`hashSpec` as the hash: the record digest the code computes.

Part 1:

* `CheckedStore.no_collision`: no two different records in a store have the same digest.
* `CheckedStore.fetched`: a store holds everything its heads reach, and nothing else.
* `CheckedStore.agree`: two stores with the same heads hold the same records, or two records
  across the two stores have the same digest (a SHA-256 collision).

Part 2 (proofs in `Refine.lean`):

* `CheckedStore.abs_accept`: what each result of `accept` means (`AcceptMeans`).
* `CheckedStore.abs_merge`: a merged store holds the records of both stores.
* `CheckedStore.encode_open`: a store's blob opens as exactly that store.
* `CheckedStore.confirmed`: what a live message's links reach is the same in your store and in
  the sender's, or there is a collision.
* `CheckedStore.classify_spec`: `CLASSIFY` gives each stored record the spec's status
  (`StatusMeans`, proofs in `Classify.lean` and `ClassifyFast.lean`).

TODO (other lanes): `open_iff`, `salvage_spec` (in `LoadApi.lean`, lane
build/encode-proofs-api), `encode_injective` (`EncodeProofs.lean`).

**What the statements mean depends on** (the trusted surface, beyond the code under test):
`abs`, `toSpec`, `hashSpec` (`Bridge.lean`); the spec's `accept`, `digests`, `heads`, `Reach`,
`Fetched`, `CollisionIn` (`Defs.lean`); `AcceptMeans` (here). For `classify_spec` also:
`liveOf`, `StatusMeans` (`Classify.lean`), and the spec's `liveRecords`, `authorConfirmed`,
`foreignMarked`, `holders` (`Chat.lean`).
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

/-! ## Part 2: accept, merge, encode, confirmation -/

/-- **What the result of `accept c r` means**, for the new store `c'`:

* `accepted d`: the spec store of `c'` is the spec's `accept` of `toSpec r` (the record is added,
  since its links resolve; it may have been there already), and `d` is the record's digest.
* `missing ds`: nothing changed; `ds` is not empty, and it is exactly the links of `r` that are
  not the digest of any record in the store.
* `collision d`: nothing changed; `d` is the digest of `r`, and the store holds a different
  record with that digest.
* `wrongChat`: nothing changed; `r` belongs to another chat.
* `tooLarge`: nothing changed; `r` has too many links, or it is new and the store is full. -/
def AcceptMeans (c : CheckedStore) (r : Rec) : AcceptResult × CheckedStore → Prop
  | (.accepted d, c') =>
    abs c' = Crdt.Merkle.accept hashSpec (abs c) (toSpec r) ∧ d = hashRecord r
  | (.missing ds, c') =>
    c' = c ∧ ds ≠ #[] ∧ ∀ x, x ∈ ds ↔ x ∈ (toSpec r).links ∧ x ∉ digests hashSpec (abs c)
  | (.collision d, c') =>
    c' = c ∧ d = hashRecord r ∧ ∃ x ∈ abs c, hashSpec x = d ∧ x ≠ toSpec r
  | (.wrongChat, c') => c' = c ∧ r.group ≠ c.group
  | (.tooLarge, c') =>
    c' = c ∧ (¬ r.WellSized ∨ (hashRecord r ∉ digests hashSpec (abs c) ∧ maxRecords ≤ c.size + 1))

-- A `missing` result with an empty list, or one that changes the store, means nothing.
example (c : CheckedStore) (r : Rec) : ¬ AcceptMeans c r (.missing #[], c) := by
  simp [AcceptMeans]

/-- **`accept`, in the spec model.** Every result of `accept` means what `AcceptMeans` says: an
accepted record is the spec's `accept`; any other result leaves the store as it was and gives
the reason. The `missing` list is exact. -/
theorem CheckedStore.abs_accept (c : CheckedStore) (r : Rec) : AcceptMeans c r (c.accept r) := by
  rcases h : c.accept r with ⟨res, c'⟩
  cases res with
  | accepted d => exact CheckedStore.abs_accept_accepted h
  | missing ds =>
    obtain ⟨h1, -, h2, h3, -⟩ := CheckedStore.abs_accept_missing h
    exact ⟨h1, h2, h3⟩
  | collision d => exact CheckedStore.abs_accept_collision h
  | wrongChat => exact CheckedStore.abs_accept_wrongChat h
  | tooLarge => exact CheckedStore.abs_accept_tooLarge h

/-- **A merged store holds the records of both stores.** -/
theorem CheckedStore.abs_merge {c d e : CheckedStore} (h : c.merge d = .ok e) :
    abs e = abs c ∪ abs d :=
  CheckedStore.merge_abs h

/-- **A store's blob opens as exactly that store** (`=` compares contents: the maps are
extensional). -/
theorem CheckedStore.encode_open (c : CheckedStore) : CheckedStore.open c.group c.encode = .ok c :=
  CheckedStore.encode_reopens c

/-- **Confirmation: "held by the sender"** (docs/PLAN.md §3.2). A live message links the digests
`hs`, and both your store `c` and the sender's store `d` hold every one of them. Then the
digests the links reach are the same in both stores. Or two different records, across the two
stores, have the same digest. (`Refine.confirmed_records` also gives the same record for each
digest.) This says the sender holds these records; it says nothing about who wrote them. -/
theorem CheckedStore.confirmed (c d : CheckedStore) (hs : Array Digest)
    (hc : ∀ h ∈ hs, c.has h = true) (hd : ∀ h ∈ hs, d.has h = true) :
    c.reachSet hs = d.reachSet hs ∨ CollisionIn hashSpec (abs c ∪ abs d) :=
  (CheckedStore.confirmed_records c d hs hc hd).imp_left And.left

/-! ### Part 2 examples

Each statement on a concrete input, with every hypothesis discharged. -/

example : AcceptMeans (CheckedStore.empty Examples.group) Examples.a1
    ((CheckedStore.empty Examples.group).accept Examples.a1) :=
  CheckedStore.abs_accept _ _

-- Bob's reply `b1` is offered to the empty store: it is `missing` exactly `a1`'s digest.
example : ((CheckedStore.empty Examples.group).accept Examples.b1).1 =
    .missing #[hashRecord Examples.a1] := by
  decide +kernel

/-- Merging the empty store into the empty store succeeds (computed by the kernel). -/
theorem Examples.merge_empty_ok :
    ((CheckedStore.empty Examples.group).merge (CheckedStore.empty Examples.group)).toBool =
      true := by
  decide +kernel

example : ∃ e, (CheckedStore.empty Examples.group).merge (CheckedStore.empty Examples.group) =
    .ok e ∧ abs e = abs (CheckedStore.empty Examples.group) ∪
      abs (CheckedStore.empty Examples.group) := by
  have h := Examples.merge_empty_ok
  revert h
  cases hm : (CheckedStore.empty Examples.group).merge (CheckedStore.empty Examples.group) with
  | ok e => exact fun _ => ⟨e, rfl, CheckedStore.abs_merge hm⟩
  | error _ => simp [Except.toBool]

example : CheckedStore.open Examples.s1.group Examples.s1.encode = .ok Examples.s1 :=
  Examples.s1.encode_open

example : Examples.s1.reachSet #[hashRecord Examples.a1] =
      Examples.s2.reachSet #[hashRecord Examples.a1] ∨
    CollisionIn hashSpec (abs Examples.s1 ∪ abs Examples.s2) :=
  CheckedStore.confirmed _ _ _ (fun h hh => by simp at hh; subst hh; exact Examples.s1_has_a1)
    (fun h hh => by simp at hh; subst hh; exact Examples.s2_has_a1)

/-! ## Part 3: who confirmed a record -/

/-- **`CLASSIFY` computes the spec's provenance status** (docs/PLAN.md §3.5). `classify c facts`
gives digest `d` the status `st` exactly when `d` is the digest of a stored record `r` and `st`
means, for `r`, what the spec says: `confirmedByAuthor` when `r` is confirmed by its author
(`authorConfirmed`); otherwise `notConfirmedByAuthor` when it has the foreign marker
(`foreignMarked`); otherwise `heldBy a` with `a` the smallest member (byte order) whose live
records reach `r` (`holders`); otherwise `unconfirmed`. The spec's live facts are read from the
host's facts (`liveOf`). -/
theorem CheckedStore.classify_spec (c : CheckedStore) (facts : Array Fact) (d : Digest)
    (st : Zrdt.Status) :
    (classify c facts)[d]? = some st ↔
      ∃ r, c.get d = some r ∧ StatusMeans (abs c) (liveOf facts) (toSpec r) st :=
  classify_getElem?_iff c facts d st

example (facts : Array Fact) (d : Digest) (st : Zrdt.Status) :
    (classify Examples.s1 facts)[d]? = some st ↔
      ∃ r, Examples.s1.get d = some r ∧
        StatusMeans (abs Examples.s1) (liveOf facts) (toSpec r) st :=
  CheckedStore.classify_spec _ _ _ _

/-- `s1` holds `a1` under its digest (computed by the kernel). -/
theorem Examples.s1_get_a1 : Examples.s1.get (hashRecord Examples.a1) = some Examples.a1 := by
  decide +kernel

-- With no facts, Alice's `a1` in `s1` is `unconfirmed`, and `CLASSIFY` cannot say otherwise.
example : (classify Examples.s1 #[])[hashRecord Examples.a1]? = some .unconfirmed := by
  rw [CheckedStore.classify_spec]
  refine ⟨_, Examples.s1_get_a1, ?_⟩
  simp [StatusMeans, authorConfirmed, foreignMarked, holders, liveRecords, liveOf, liveList]

example : (classify Examples.s1 #[])[hashRecord Examples.a1]? ≠ some .confirmedByAuthor := by
  intro h
  obtain ⟨r, -, hs⟩ := (CheckedStore.classify_spec _ _ _ _).mp h
  simp [StatusMeans, authorConfirmed, liveRecords, liveOf, liveList] at hs

-- Once `a1` is known to have arrived live, it is confirmed by its author.
example : (classify Examples.s1 #[⟨hashRecord Examples.a1, .live, #[]⟩])[hashRecord Examples.a1]? =
    some .confirmedByAuthor := by
  rw [CheckedStore.classify_spec]
  refine ⟨_, Examples.s1_get_a1, ?_⟩
  have hmem : toSpec Examples.a1 ∈ abs Examples.s1 :=
    ((Examples.s1.get_eq_some_iff).mp Examples.s1_get_a1).1
  exact ⟨⟨toSpec Examples.a1, Finset.mem_filter.mpr ⟨hmem, by simp [liveOf, liveList], rfl⟩,
    .head (Finset.mem_singleton_self _)⟩, fun y _ => by simp [liveOf, liveList]⟩

-- A record with no live record anywhere is `unconfirmed`, and not `confirmedByAuthor`.
example (x : SpecRec) : StatusMeans ∅ ⟨∅, ∅⟩ x .unconfirmed ∧
    ¬ StatusMeans ∅ ⟨∅, ∅⟩ x .confirmedByAuthor := by
  simp [StatusMeans, authorConfirmed, foreignMarked, holders, liveRecords]

end Zrdt
