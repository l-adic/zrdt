/-
Copyright (c) 2026 zrdt contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: zrdt contributors
-/
import Mathlib
import Crdt.Merkle.Bridge
import Crdt.Merkle.Refine
import Crdt.Merkle.ClassifyFast
import Crdt.Merkle.ClassifyStatus
import Crdt.Merkle.EncodeProofs
import Crdt.Merkle.LoadApi

set_option linter.unusedSectionVars false

/-!
# What the shipped store guarantees (docs/PLAN.md §3.2)

These are the advertised statements about the shipped code, `Zrdt.CheckedStore`, and nothing
else is advertised. The axiom gate (`Test/Axioms.lean`) pins exactly these names. Each one is
about `abs c`, the set of records the store holds, seen in the spec model (`Bridge.lean`), with
`hashSpec` as the hash: the record digest the code computes. Each is a one-line corollary of a
proof in `Bridge.lean`, `Refine.lean`, `LoadApi.lean`, `EncodeProofs.lean`,
`ClassifyStatus.lean` or the spec (`Defs.lean`, `Chat.lean`).

In the order of docs/PLAN.md §3.2:

* `CheckedStore.fetched`: a store holds everything its heads reach, and nothing else.
* `CheckedStore.no_collision`: no two different records in a store have the same digest.
* `CheckedStore.agree`: two stores with the same heads hold the same records, or two records
  across the two stores have the same digest (a SHA-256 collision).
* `CheckedStore.abs_accept`: what each result of `accept` means (`AcceptMeans`).
* `CheckedStore.abs_merge`: a merged store holds the records of both stores.
* `CheckedStore.open_iff`: when `OPEN` loads a blob, and what store it gives.
* `CheckedStore.salvage_spec`: what `SALVAGE` keeps (the model's `buildRetry`) and what it drops.
* `CheckedStore.encode_open`: a store's blob opens as exactly that store.
* `CheckedStore.confirmed`: what a live message's links reach is the same in your store and in
  the sender's, or there is a collision.
* `CheckedStore.classify_spec`: `CLASSIFY` gives each stored record the spec's `status`
  (`Chat.lean`), and nothing else a status.
* `Zrdt.encode_injective`: different records have different encodings. It is declared in
  `EncodeProofs.lean` and not restated here; it is pinned by the gate with the others.

**Differences from the text of PLAN §3.2** (the same statements, made precise):

* `u.map toSpec` (an array) is written `specOf u`, the set of the records of `u` (`Refine.lean`).
  So a record repeated in a blob counts once, and the order of the records does not matter.
* `salvage_spec` needs only that the blob decodes to `u`; it concludes that `u` has no collision,
  that the store is of the right chat, and that `dropped` is sorted.
* `confirmed` asks `c.has h = true` for each `h ∈ hs` (PLAN: `hs ⊆ c.keys`).
* `open_iff` and `salvage_spec` are about `decodeBlob` as it is, so they do not depend on how it
  frames records (lane T5: a count of `2^24` or more is refused, records in any order, repeats
  allowed). `classify_spec` is stated with the spec's `status`, which names one holder, the
  smallest (lead decision 1 of 2026-11-01, lane T5's `Chat.lean`); account ids are ordered byte
  by byte (`Aci.instLinearOrder`, `ClassifyStatus.lean`), the order the code uses.

**What the statements mean depends on** (the trusted surface, beyond the code under test):
`abs`, `toSpec`, `hashSpec` (`Bridge.lean`); `specOf`, `AcceptMeans` (`Refine.lean`); the spec's
`accept`, `digests`, `heads`, `Reach`, `Fetched`, `CollisionIn` (`Defs.lean`) and `AcceptBuilt`,
`buildRetry` (`Chat.lean`); `WellSized`, `decodeBlob`, `encode` (`core/Zrdt/Encode.lean`).
For `classify_spec` also: `liveOf` (`Classify.lean`), `Status.toSpec` and the order on `Aci`
(`ClassifyStatus.lean`), and the spec's `status`, `liveRecords`, `authorConfirmed`,
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
    abs c = abs d ∨ CollisionIn hashSpec (abs c ∪ abs d) :=
  fetched_agree hashSpec c.fetched (CheckedStore.specHeads_eq_of_heads_eq h ▸ d.fetched)

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

/-! ## Part 2: accept, merge, open, salvage, encode, confirmation -/

/-- **`accept`, in the spec model.** Every result of `accept` means what `AcceptMeans` says: an
accepted record is the spec's `accept`; any other result leaves the store as it was and gives
the reason. The `missing` list is exact. -/
theorem CheckedStore.abs_accept (c : CheckedStore) (r : Rec) : AcceptMeans c r (c.accept r) :=
  CheckedStore.accept_means c r

/-- **A merged store holds the records of both stores.** -/
theorem CheckedStore.abs_merge {c d e : CheckedStore} (h : c.merge d = .ok e) :
    abs e = abs c ∪ abs d :=
  CheckedStore.merge_abs h

/-- **`OPEN`, in the spec model.** `open g b` loads the store `c` exactly when `b` decodes to
chat `g` and records `u` that are within the size limits (`WellSized`), can be accepted in some
order (`AcceptBuilt`: every link points to a record accepted before), have no collision and are
all of chat `g`; and then `c` is the store of chat `g` holding exactly the records of `u`. -/
theorem CheckedStore.open_iff {g : GroupId} {b : ByteArray} {c : CheckedStore} :
    CheckedStore.open g b = .ok c ↔
      ∃ u, decodeBlob b = some (g, u) ∧ WellSized u ∧ AcceptBuilt hashSpec (specOf u) ∧
        ¬ CollisionIn hashSpec (specOf u) ∧ (∀ r ∈ u, r.group = g) ∧ abs c = specOf u ∧
        c.group = g :=
  CheckedStore.open_ok_iff_model

/-- **`SALVAGE`, in the spec model.** If `salvage g b` loads `s`, and the blob `b` holds the
records `u`, then `u` has no collision, the store holds exactly what the model's salvage keeps
(`buildRetry`: accept what can be accepted, in any order, until nothing more can), it is of chat
`g`, and `dropped` is sorted and holds exactly the digests of the other records of `u`. -/
theorem CheckedStore.salvage_spec {g : GroupId} {b : ByteArray} {s : Salvaged} {u : Array Rec}
    (h : salvage g b = .ok s) (hu : decodeBlob b = some (g, u)) :
    ¬ CollisionIn hashSpec (specOf u) ∧
      abs s.store = buildRetry hashSpec (specOf u) ∧ s.store.group = g ∧
      (∀ d, d ∈ s.dropped ↔ d ∈ digests hashSpec (specOf u \ buildRetry hashSpec (specOf u))) ∧
      StrictlySorted s.dropped :=
  CheckedStore.salvage_ok_model h hu

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

-- `open_iff`, forwards, on the blob of `s1`: it decodes to records that are accept-built, have
-- no collision, and are exactly the records of `s1`.
example : ∃ u, decodeBlob Examples.s1.encode = some (Examples.s1.group, u) ∧ WellSized u ∧
    AcceptBuilt hashSpec (specOf u) ∧ ¬ CollisionIn hashSpec (specOf u) ∧
    (∀ r ∈ u, r.group = Examples.s1.group) ∧ abs Examples.s1 = specOf u ∧
    Examples.s1.group = Examples.s1.group :=
  CheckedStore.open_iff.mp Examples.s1.encode_open

-- `open_iff` rejects a bad blob: a blob holding only Bob's reply `b1` (the message `a1` it links
-- cut out) opens as no store at all, since `{b1}` is not accept-built.
example (c : CheckedStore) :
    CheckedStore.open Examples.group (encodeBlob Examples.group #[Examples.b1]) ≠ .ok c := by
  intro h
  obtain ⟨u, hu, -, hab, -⟩ := CheckedStore.open_iff.mp h
  rw [decodeBlob_encodeBlob _ _ (by decide +kernel)] at hu
  simp only [Option.some.injEq, Prod.mk.injEq, true_and] at hu
  subst hu
  exact Examples.b1_alone_not_acceptBuilt hab

/-- The digests of `a1`, `c1` and `a2` differ (computed by the kernel). -/
theorem Examples.hash_a1_ne_c1 : hashRecord Examples.a1 ≠ hashRecord Examples.c1 := by
  decide +kernel

/-- See `hash_a1_ne_c1`. -/
theorem Examples.hash_a1_ne_a2 : hashRecord Examples.a1 ≠ hashRecord Examples.a2 := by
  decide +kernel

/-- See `hash_a1_ne_c1`. -/
theorem Examples.hash_c1_ne_a2 : hashRecord Examples.c1 ≠ hashRecord Examples.a2 := by
  decide +kernel

-- `salvage_spec` on the doctored restore of the demo (`Examples.doctored`: the blob of `all4`
-- with `b1` cut out, so `a2` links a record that is not there). Salvage succeeds; it keeps
-- exactly what the model's `buildRetry` keeps and drops exactly the digests of the rest.
example : ∃ s, CheckedStore.salvage Examples.group Examples.doctored = .ok s ∧
    abs s.store = buildRetry hashSpec (specOf #[Examples.a1, Examples.c1, Examples.a2]) ∧
    ∀ d, d ∈ s.dropped ↔ d ∈ digests hashSpec
      (specOf #[Examples.a1, Examples.c1, Examples.a2] \
        buildRetry hashSpec (specOf #[Examples.a1, Examples.c1, Examples.a2])) := by
  have hw : WellSized #[Examples.a1, Examples.c1, Examples.a2] := by decide +kernel
  have hdec : decodeBlob Examples.doctored =
      some (Examples.group, #[Examples.a1, Examples.c1, Examples.a2]) :=
    decodeBlob_encodeBlob _ _ hw
  have hg : ∀ r ∈ #[Examples.a1, Examples.c1, Examples.a2], r.group = Examples.group := by
    intro r hr
    simp only [List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> rfl
  have hcol : NoCollision #[Examples.a1, Examples.c1, Examples.a2] := by
    intro x hx y hy hxy
    simp only [List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at hx hy
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
    · rfl
    · exact absurd hxy Examples.hash_a1_ne_c1
    · exact absurd hxy Examples.hash_a1_ne_a2
    · exact absurd hxy.symm Examples.hash_a1_ne_c1
    · rfl
    · exact absurd hxy Examples.hash_c1_ne_a2
    · exact absurd hxy.symm Examples.hash_a1_ne_a2
    · exact absurd hxy.symm Examples.hash_c1_ne_a2
    · rfl
  obtain ⟨s, hs⟩ := CheckedStore.salvage_ok_of hdec hw hg hcol
  obtain ⟨-, habs, -, hdrop, -⟩ := CheckedStore.salvage_spec hs hdec
  exact ⟨s, hs, habs, hdrop⟩

example : Examples.s1.reachSet #[hashRecord Examples.a1] =
      Examples.s2.reachSet #[hashRecord Examples.a1] ∨
    CollisionIn hashSpec (abs Examples.s1 ∪ abs Examples.s2) :=
  CheckedStore.confirmed _ _ _ (fun h hh => by simp at hh; subst hh; exact Examples.s1_has_a1)
    (fun h hh => by simp at hh; subst hh; exact Examples.s2_has_a1)

/-! ## Part 3: who confirmed a record -/

/-- **`CLASSIFY` computes the spec's provenance status** (docs/PLAN.md §3.5). `classify c facts`
gives digest `d` the status `st` exactly when `d` is the digest of a stored record `r` and `st`
is the spec's `status` of `r` (`Chat.lean`): `confirmedByAuthor` when `r` is confirmed by its
author (`authorConfirmed`); otherwise `notConfirmedByAuthor` when it has the foreign marker
(`foreignMarked`); otherwise `heldBy a` with `a` the smallest member (byte order) whose live
records reach `r` (`holders`); otherwise `unconfirmed`. The spec's live facts are read from the
host's facts (`liveOf`); `Status.toSpec` reads the code's label as the spec's (the same label).
-/
theorem CheckedStore.classify_spec (c : CheckedStore) (facts : Array Fact) (d : Digest)
    (st : Zrdt.Status) :
    (classify c facts)[d]? = some st ↔
      ∃ r, c.get d = some r ∧
        Crdt.Merkle.status hashSpec (abs c) (liveOf facts) (toSpec r) = st.toSpec :=
  CheckedStore.classify_eq_some_iff c facts d st

example (facts : Array Fact) (d : Digest) (st : Zrdt.Status) :
    (classify Examples.s1 facts)[d]? = some st ↔
      ∃ r, Examples.s1.get d = some r ∧
        Crdt.Merkle.status hashSpec (abs Examples.s1) (liveOf facts) (toSpec r) = st.toSpec :=
  CheckedStore.classify_spec _ _ _ _

-- With no facts, Alice's `a1` in `s1` is `unconfirmed`, and `CLASSIFY` cannot say otherwise.
example : (classify Examples.s1 #[])[hashRecord Examples.a1]? = some .unconfirmed := by
  rw [CheckedStore.classify_spec]
  refine ⟨_, Examples.s1_get_a1, ?_⟩
  simp [Crdt.Merkle.status, Status.toSpec, authorConfirmed, foreignMarked, holders, liveRecords,
    liveOf, liveList]

example : (classify Examples.s1 #[])[hashRecord Examples.a1]? ≠ some .confirmedByAuthor := by
  intro h
  obtain ⟨r, hr, hs⟩ := (CheckedStore.classify_spec _ _ _ _).mp h
  rw [Examples.s1_get_a1, Option.some.injEq] at hr
  subst hr
  simp [Crdt.Merkle.status, Status.toSpec, authorConfirmed, foreignMarked, holders, liveRecords,
    liveOf, liveList] at hs

-- Once `a1` is known to have arrived live, it is confirmed by its author.
example : (classify Examples.s1 #[⟨hashRecord Examples.a1, .live, #[]⟩])[hashRecord Examples.a1]? =
    some .confirmedByAuthor := by
  rw [CheckedStore.classify_spec]
  refine ⟨_, Examples.s1_get_a1, ?_⟩
  have hmem : toSpec Examples.a1 ∈ abs Examples.s1 :=
    ((Examples.s1.get_eq_some_iff).mp Examples.s1_get_a1).1
  have hac : authorConfirmed hashSpec (abs Examples.s1)
      (liveOf #[⟨hashRecord Examples.a1, .live, #[]⟩]) (toSpec Examples.a1) :=
    ⟨⟨toSpec Examples.a1, Finset.mem_filter.mpr ⟨hmem, by simp [liveOf, liveList], rfl⟩,
      .head (Finset.mem_singleton_self _)⟩, fun y _ => by simp [liveOf, liveList]⟩
  simp [Crdt.Merkle.status, Status.toSpec, hac]

-- A record with no live record anywhere is `unconfirmed` (so not `confirmedByAuthor`).
example (x : SpecRec) : Crdt.Merkle.status hashSpec ∅ ⟨∅, ∅⟩ x = .unconfirmed := by
  simp [Crdt.Merkle.status, authorConfirmed, foreignMarked, holders, liveRecords]

/-! ## The encoding

`Zrdt.encode_injective` (`EncodeProofs.lean`, pinned by the gate): different records have
different encodings, for every record, with no size bound. -/

-- Alice's `a1` and Bob's `b1` are different records, so their encodings differ.
example : encode Examples.a1 ≠ encode Examples.b1 :=
  fun h => by have := encode_injective h; revert this; decide +kernel

end Zrdt
