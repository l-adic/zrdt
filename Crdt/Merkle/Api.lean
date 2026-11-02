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
import Crdt.Merkle.ServeAbs
import Crdt.Merkle.ServeAbsRel
import Crdt.Merkle.AppsBase
import Crdt.Merkle.AppsTorrent
import Crdt.Merkle.AppsGit

set_option linter.unusedSectionVars false

/-!
# What the shipped store guarantees (docs/PLAN.md §3.2)

These are the advertised statements about the shipped code, `Zrdt.CheckedStore`, and nothing
else is advertised. The axiom gate (`Test/Axioms.lean`) pins exactly these names, and
`Comparator/Challenge.lean` restates them word for word for `lake comparator`
(`comparator.json`): a change to a statement here must be made there too. Each one is
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

Added for joining (docs/JOIN_PLAN.md §7.3):

* `CheckedStore.agree_rel`: a view with a boundary (a newcomer's store) that has the same heads
  as a store, seen with a boundary, holds only that store's records under every digest its heads
  reach, or two records collide. Nothing is assumed about the view's own boundary.
* `CheckedStore.serve_content`: every opening in `SERVE`'s reply opens a record of the store, and
  its own committed audience seats the requester's account under the key `SERVE` checked.
* `CheckedStore.serve_content_complete`: the converse; every held opening that `serveOpening`
  accepts for a record of the store goes out, when the request asks for that record.

The statements for a store with a boundary (`RelStore`, a newcomer's store; JOIN_PLAN §7.3),
one for each of the closed statements above, with the same name in the namespace `RelStore`
(Part 5). Each is about `c.raw.abs`, the store's records in the spec model, and `boundarySet
c.boundary`, the digests it holds no record for; with the empty boundary each says what the closed
statement says (examples in Part 5):

* `RelStore.fetched`: everything the heads reach is a stored digest or a boundary digest, and
  every stored record is reached from the heads, when the records have no cycle.
* `RelStore.no_collision`: no two different records in the store have the same digest.
* `RelStore.agree`: two stores with the same heads hold the same records, when neither holds a
  record whose digest the other has only as a boundary digest and neither has a cycle; or two
  records collide.
* `RelStore.abs_accept`: what each result of `accept` means (`AcceptRelMeans`).
* `RelStore.abs_merge`: a merged store holds the records of both stores and knows the digests both
  know.
* `RelStore.open_iff`: when `load` (`OPEN` of a relative blob) gives a store, and which.
* `RelStore.salvage_spec`: what `SALVAGE` of a relative blob keeps (`buildRetryRel`) and drops.
* `RelStore.encode_open`: a relative store's blob opens as exactly that store.
* `RelStore.confirmed`: what a live message's links reach in your store is reached in the
  sender's store too, except below a digest the sender holds only as a boundary digest; or two
  records collide.
* `RelStore.classify_spec`: `CLASSIFY` on a relative store without a cycle gives each stored
  record the spec's `status`, and nothing else a status.

The apps (docs/apps/BUILD_M1.md §C), Part 6: one section per lane (`[lane base]`,
`[lane torrent]`, `[lane git]`), each listing its advertised statements in its own doc comment.
Each lane edits only its own section; the proofs live in `Crdt/Merkle/Apps*.lean` and
`core/Zrdt/{AppBase,Torrent,Git,Apps}.lean`.
* `encode_injective` is about the encoding of one record: no store, so no boundary, enters, and
  it holds for records of a relative store as stated.

The statements added for joining, for a responder with a boundary (a former newcomer re-serves):

* `RelStore.agree_rel`: `CheckedStore.agree_rel` with the store's own boundary as `BS`; a view
  with the store's heads holds only its records under every digest its heads reach.
* `RelStore.serve_content`, `RelStore.serve_content_complete`: as for a closed store; `SERVE`
  reads only the stored records, the held openings and the request, so the boundary changes
  nothing in which openings go.

**Differences from the text of PLAN §3.2** (the same statements, made precise):

* `u.map toSpec` (an array) is written `specOf u`, the set of the records of `u` (`Refine.lean`).
  So a record repeated in a blob counts once, and the order of the records does not matter.
* `salvage_spec` needs only that the blob decodes to `u`; it concludes that `u` has no collision,
  that the store is of the right chat, and that `dropped` is sorted.
* `confirmed` asks `c.has h = true` for each `h ∈ hs` (PLAN: `hs ⊆ c.keys`).
* JOIN_PLAN §7.3 names the content theorem `Serve.serve_content`. That name is the running-code
  theorem in `core/Zrdt/Serve.lean`, stated with `c.get d = some r`; the Comparator challenge
  must import that module for `serve`, so it cannot restate the name. The advertised form is
  `CheckedStore.serve_content`, stated with `toSpec r ∈ abs c` like the other statements here.
  The same holds for `serve_content_complete`, whose `since` is the spec's `Reach`.
* `agree_rel` takes the store's boundary `BS` as an argument: a closed store has `BS = ∅`, and a
  responder that is a former newcomer passes its own boundary to `SERVE`.
* **Part 5, what is new for a boundary** (each needed; the counterexample is checked):
  two stores can have the same heads and differ below a boundary (`below_boundary_not_vouched`,
  `Rel.lean`), so `RelStore.agree` assumes neither holds a record whose digest the other has only
  as a boundary digest; a store with a boundary can have a cycle without a collision, through a
  record whose digest was a boundary digest (`promoted_cycle`, `promoted_cycle_not_tight`,
  `RelSpec.lean`), so `fetched`, `agree` and `classify_spec` assume `Acyclic`
  (`BuiltRel.acyclic_of_unpromoted` gives it when no record was promoted; for SHA-256 a cycle
  needs a record whose digest was written into a record its own digest depends on); and
  `confirmed` holds only up to the sender's boundary (`reach_transfer`). `open_iff` and
  `salvage_spec` are about the store-level `load` and `salvage` (the relative branch of
  `ChatStore.openStore` and `ChatStore.salvageChat`); `encode_open` is about the `zrdtS3` blob
  (`ChatStore.encodeChat`, `openChat`).
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
`foreignMarked`, `holders` (`Chat.lean`). For `agree_rel` also: `headsRel`, `inView`,
`linksOf` (`Rel.lean`). For `serve_content` and `serve_content_complete` also: `serve`,
`serveOpening`, `authorCopy`, `audienceOf`, `seats`, `keyTag`, `ephemeral` and what they call
(`core/Zrdt/Serve.lean`), and `openingMatches` (`core/Zrdt/Commit.lean`). For Part 5 also:
`boundarySet`, `AcceptRelMeans` (`RelBridge.lean`); `acceptRel`, `AcceptBuiltRel`, `buildRetryRel`
(`RelSpec.lean`); `Acyclic` (`ClassifyFast.lean`); `inView`, `headsRel` (`Rel.lean`); `Tight`
(`Defs.lean`); and the code they read: `RelStore` and its `accept`, `merge`, `load`, `salvage`,
`boundaryDigests` (`core/Zrdt/RelStore.lean`), `classifyRaw` (`core/Zrdt/Provenance.lean`),
`openChat`, `encodeChat`, `storedAudiences` and what they call (`core/Zrdt/ChatStore.lean`).
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

/-- Alice's store: her message `a1`, then Bob's reply `b1`, then Carol's reply `c1`. -/
def Examples.aliceStore : CheckedStore :=
  ((((CheckedStore.empty Examples.group).accept Examples.a1).2.accept Examples.b1).2.accept
    Examples.c1).2

/-- Bob's store: the same three records, the two replies in the other order. -/
def Examples.bobStore : CheckedStore :=
  ((((CheckedStore.empty Examples.group).accept Examples.a1).2.accept Examples.c1).2.accept
    Examples.b1).2

/-- The two stores were built in different orders, and they have the same heads (`b1` and
`c1`). The kernel computes both lists of heads; equal lists give equal sets. -/
theorem Examples.aliceStore_heads_eq_bobStore : Examples.aliceStore.heads = Examples.bobStore.heads := by
  have hl : Examples.aliceStore.heads.toList = Examples.bobStore.heads.toList := by
    decide +kernel
  apply Std.ExtTreeSet.ext_mem
  intro x
  rw [← Std.ExtTreeSet.mem_toList, ← Std.ExtTreeSet.mem_toList, hl]

-- `agree` on two stores built in different orders: same heads, so the same records (or a
-- collision).
example : abs Examples.aliceStore = abs Examples.bobStore ∨
    CollisionIn hashSpec (abs Examples.aliceStore ∪ abs Examples.bobStore) :=
  CheckedStore.agree _ _ Examples.aliceStore_heads_eq_bobStore

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
accepted record is the spec's `accept`, every link of it is the digest of a record the store
already held, and the record is in the new store; any other result leaves the store as it was
and gives the reason. The `missing` list is exact. -/
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

/-! ## Part 4: joining (docs/JOIN_PLAN.md §7.3) -/

/-- **Same heads, same history, for a view with a boundary** (JOIN_PLAN §6.7, §7.2). A view is a
set of records `F` and a set of boundary digests `B`: a newcomer's store, which holds only the
digests of older records. Take a checked store `c`, seen with boundary digests `BS` (`∅` for a
store `zrdtd` holds). Suppose the view has the same heads as `c` with `BS`, and holds no record
whose digest is in `BS` but not stored in `c`. Then each digest reachable from the view's heads
is either the digest of a record of `c`, and every record of the view with that digest is in
`c`; or a digest of `BS` only, for which the view holds no record. Or two records, across `c`
and the view, have the same digest. Nothing is assumed about `B`. -/
theorem CheckedStore.agree_rel (c : CheckedStore) (BS : Finset Digest) {F : SpecStore}
    {B : Finset Digest} (hh : headsRel hashSpec F B = headsRel hashSpec (abs c) BS)
    (hFB : ∀ r ∈ F, hashSpec r ∈ BS → hashSpec r ∈ digests hashSpec (abs c)) :
    ∀ d, Reach hashSpec F (headsRel hashSpec F B) d →
      (d ∈ digests hashSpec (abs c) ∧ ∀ r ∈ F, hashSpec r = d → r ∈ abs c) ∨
        (d ∈ BS ∧ d ∉ digests hashSpec (abs c) ∧ ∀ r ∈ F, hashSpec r ≠ d) ∨
        CollisionIn hashSpec (abs c ∪ F) :=
  agree_rel' hashSpec (c.closedRel BS) hh hFB

/-- **Content goes only where its author sent it** (JOIN_PLAN §7.1). Every opening in `SERVE`'s
reply to `q` from the store `c` opens a record of `c`, and that opening's own committed audience
(`DataMessage` field 201) seats `q`'s account under the tag of `q`'s identity key: the key the
host seals the reply to. No audience cache, no `since`, no strict or export flag, and no
provenance enters, so none of them can widen it. -/
theorem CheckedStore.serve_content (c : CheckedStore) {me : Serve.Me} {held : Serve.HeldMap}
    {q : Serve.Query} {r : Rec} {op : ByteArray} {ac : Bool}
    (he : Serve.Entry.addressed r (some op) ac ∈ Serve.serve c.raw me held q) :
    toSpec r ∈ abs c ∧ openingMatches r.group r.author r.commit op = true ∧
      ∃ aud, Serve.audienceOf op = some aud ∧ Serve.seats aud q.aci q.key = true := by
  obtain ⟨d, hget, h⟩ := Serve.serve_content he
  exact ⟨((c.get_eq_some_iff).mp hget).1, h op rfl⟩

/-- **Content that may go, goes** (JOIN_PLAN §7.1, the converse of `serve_content`). Take a record
`r` of the store `c` and an opening the responder holds for it that `serveOpening` accepts (it
opens `r`, its own audience seats `q`, it is not ephemeral in an export, and in strict mode `r`
is the responder's own copy). If the request is a catch-up whose `since` does not reach `r`, or
a per-digest request that asks for `r`, then the reply carries `r` with that opening, marked
author copy exactly when it is one. -/
theorem CheckedStore.serve_content_complete (c : CheckedStore) {me : Serve.Me}
    {held : Serve.HeldMap} {q : Serve.Query} {r : Rec} {op : ByteArray}
    (hr : toSpec r ∈ abs c) (hop : (held.getD (hashRecord r) {}).opening = some op)
    (hs : Serve.serveOpening me q (hashRecord r) r op = true)
    (hmode : (q.wanted = none ∧
        ¬ Reach hashSpec (abs c) (q.since ++ q.ownSince).toList.toFinset (hashRecord r)) ∨
      ∃ ws, q.wanted = some ws ∧ hashRecord r ∈ ws) :
    Serve.Entry.addressed r (some op) (Serve.authorCopy me (hashRecord r) r) ∈
      Serve.serve c.raw me held q := by
  have hget : c.raw.map[hashRecord r]? = some r := (c.get_eq_some_iff).mpr ⟨hr, rfl⟩
  rcases hmode with ⟨hq, hn⟩ | ⟨ws, hq, hw⟩
  · refine Serve.serve_content_complete hget hop hs (by simp [hq]) (.inr ?_)
    rw [Bool.eq_false_iff, ne_eq, Std.ExtTreeSet.contains_iff_mem, Serve.mem_sinceReach]
    exact fun h => hn h.2
  · exact Serve.serve_content_complete hget hop hs (by simp [hq, hw]) (.inl (by simp [hq]))

/-! ### Part 4 examples

Each statement on a concrete input, with every hypothesis discharged, and a bad output each one
rules out. The inputs are those of `core/Zrdt/Serve.lean`: Carol's `pre` (before Bob joined),
Alice's `welcome` (Bob seated), Carol's `stale` (Bob not seated), Alice's `later` (Bob seated);
and `selfMsg`, Alice's message to herself, small enough for the kernel to hash. -/

/-- Bob's catch-up from Alice: the reply of `SERVE` for Bob, under his key, from Alice's store
with the four records. -/
def Examples.bobReply : List Serve.Entry :=
  Serve.serve Serve.Examples.checkedStore.raw Serve.Examples.meAlice Serve.Examples.held
    (Serve.Examples.rq Examples.bob Serve.Examples.keyBob)

example : Examples.bobReply = Serve.serve Serve.Examples.checkedStore.raw Serve.Examples.meAlice
    Serve.Examples.held (Serve.Examples.rq Examples.bob Serve.Examples.keyBob) := rfl

-- `agree_rel` on Bob's view after that catch-up, against Alice's store: `serve_heads` and
-- `replyRecords_subset` discharge the hypotheses.
example : ∀ d, Reach hashSpec (Serve.replyRecords Examples.bobReply)
      (headsRel hashSpec (Serve.replyRecords Examples.bobReply)
        (Serve.replyBoundary Examples.bobReply)) d →
    (d ∈ digests hashSpec (abs Serve.Examples.checkedStore) ∧
        ∀ r ∈ Serve.replyRecords Examples.bobReply, hashSpec r = d →
          r ∈ abs Serve.Examples.checkedStore) ∨
      (d ∈ Serve.boundarySpec Serve.Examples.meAlice ∧
        d ∉ digests hashSpec (abs Serve.Examples.checkedStore) ∧
        ∀ r ∈ Serve.replyRecords Examples.bobReply, hashSpec r ≠ d) ∨
      CollisionIn hashSpec
        (abs Serve.Examples.checkedStore ∪ Serve.replyRecords Examples.bobReply) :=
  Serve.Examples.checkedStore.agree_rel _ (Serve.serve_heads _ _ _ _ rfl) fun r hr _ =>
    (mem_digests hashSpec).mpr ⟨r, Serve.replyRecords_subset _ _ _ _ hr, rfl⟩

-- `agree_rel` with no boundary on either side: Bob's store and Alice's store, built in
-- different orders, have the same heads.
example : ∀ d, Reach hashSpec (abs Examples.bobStore)
      (headsRel hashSpec (abs Examples.bobStore) ∅) d →
    (d ∈ digests hashSpec (abs Examples.aliceStore) ∧
        ∀ r ∈ abs Examples.bobStore, hashSpec r = d → r ∈ abs Examples.aliceStore) ∨
      (d ∈ (∅ : Finset Digest) ∧ d ∉ digests hashSpec (abs Examples.aliceStore) ∧
        ∀ r ∈ abs Examples.bobStore, hashSpec r ≠ d) ∨
      CollisionIn hashSpec (abs Examples.aliceStore ∪ abs Examples.bobStore) := by
  refine Examples.aliceStore.agree_rel ∅ ?_ (by simp)
  rw [headsRel_empty, headsRel_empty, ← CheckedStore.heads_toFinset,
    ← CheckedStore.heads_toFinset, Examples.aliceStore_heads_eq_bobStore]

-- `agree_rel` rejects a view that holds a record the store does not: the record `first`, as a
-- view of its own, against the empty store, meets none of the three cases.
example : ¬ ∀ d, Reach hashSpec {toSpec Examples.first}
      (headsRel hashSpec {toSpec Examples.first} ∅) d →
    (d ∈ digests hashSpec (abs (CheckedStore.empty Examples.group)) ∧
        ∀ r ∈ ({toSpec Examples.first} : SpecStore), hashSpec r = d →
          r ∈ abs (CheckedStore.empty Examples.group)) ∨
      (d ∈ (∅ : Finset Digest) ∧ d ∉ digests hashSpec (abs (CheckedStore.empty Examples.group)) ∧
        ∀ r ∈ ({toSpec Examples.first} : SpecStore), hashSpec r ≠ d) ∨
      CollisionIn hashSpec (abs (CheckedStore.empty Examples.group) ∪ {toSpec Examples.first}) := by
  intro h
  have habs : abs (CheckedStore.empty Examples.group) = ∅ := by
    simp [abs, RawStore.abs, CheckedStore.empty]
  have hhead : hashSpec (toSpec Examples.first) ∈
      headsRel hashSpec {toSpec Examples.first} ∅ := by
    rw [mem_headsRel, mem_inView, mem_linksOf]
    refine ⟨.inl ⟨_, Finset.mem_singleton_self _, rfl⟩, ?_⟩
    rintro ⟨x, hx, hl⟩
    rw [Finset.mem_singleton] at hx
    subst hx
    simp [toSpec, Examples.first, Rec.make] at hl
  rw [habs] at h
  rcases h _ (.head hhead) with ⟨hd, -⟩ | ⟨hb, -⟩ | ⟨x, hx, y, hy, hne, -⟩
  · simp [digests] at hd
  · simp at hb
  · simp only [Finset.empty_union, Finset.mem_singleton] at hx hy
    exact hne (hx.trans hy.symm)

-- `serve_content` on Alice's catch-up of her message to herself (`Serve.Examples.self_served`).
example : toSpec Serve.Examples.selfMsg.1 ∈ abs Serve.Examples.selfStore ∧
    openingMatches Serve.Examples.selfMsg.1.group Serve.Examples.selfMsg.1.author
      Serve.Examples.selfMsg.1.commit Serve.Examples.selfMsg.2 = true ∧
    ∃ aud, Serve.audienceOf Serve.Examples.selfMsg.2 = some aud ∧
      Serve.seats aud (Serve.Examples.rq Examples.alice Serve.Examples.keyAlice).aci
        (Serve.Examples.rq Examples.alice Serve.Examples.keyAlice).key = true :=
  CheckedStore.serve_content Serve.Examples.selfStore (Serve.Examples.self_served false false)

-- `serve_content` rejects a reply that gives Bob the opening of `pre`, Carol's message from
-- before he joined: its committed audience seats only Alice and Carol.
example : ¬ ∃ aud, Serve.audienceOf Serve.Examples.pre.2 = some aud ∧
    Serve.seats aud Examples.bob Serve.Examples.keyBob = true := by
  rintro ⟨aud, ha, hs⟩
  have hno : (Serve.audienceOf Serve.Examples.pre.2).any
      (Serve.seats · Examples.bob Serve.Examples.keyBob) = false := by decide +kernel
  simp [ha, hs] at hno

/-- Reaching from no digest reaches nothing. -/
theorem Examples.not_reach_empty (s : SpecStore) (d : Digest) : ¬ Reach hashSpec s ∅ d :=
  fun h => by simpa using Reach.mem_of_bound hashSpec (R := ∅) subset_rfl (by simp) h

-- `serve_content_complete` on Alice's catch-up of her message to herself: every hypothesis is
-- discharged, and the reply carries it with its opening, as an author copy.
example : Serve.Entry.addressed Serve.Examples.selfMsg.1 (some Serve.Examples.selfMsg.2)
      (Serve.authorCopy Serve.Examples.selfMe (hashRecord Serve.Examples.selfMsg.1)
        Serve.Examples.selfMsg.1) ∈
    Serve.serve Serve.Examples.selfStore.raw Serve.Examples.selfMe Serve.Examples.selfHeld
      (Serve.Examples.rq Examples.alice Serve.Examples.keyAlice) :=
  Serve.Examples.selfStore.serve_content_complete
    ((Serve.Examples.selfStore.get_eq_some_iff).mp Serve.Examples.selfStore_get).1
    (by simp [Serve.Examples.selfHeld, Serve.Examples.selfDigest])
    (Serve.Examples.selfMsg_serveOpening false false)
    (.inl ⟨rfl, by simpa [Serve.Examples.rq] using Examples.not_reach_empty _ _⟩)

-- `serve_content_complete` rejects a reply that leaves that message out.
example : Serve.Entry.addressed Serve.Examples.selfMsg.1 (some Serve.Examples.selfMsg.2) true ∉
    ([] : List Serve.Entry) := List.not_mem_nil

/-! ## Part 5: a store with a boundary (docs/JOIN_PLAN.md §7.3)

The statements of Parts 1 to 3, for a newcomer's store (`RelStore`). See the module header for
what each says and what is new. -/

/-- **No collision in a store with a boundary.** Two different stored records never have the same
digest. -/
theorem RelStore.no_collision (c : RelStore) : ¬ CollisionIn hashSpec c.raw.abs :=
  c.no_collision_model

/-- **A store with a boundary is fetched from its heads.** Following links from the heads (the
stored digests and the boundary digests no stored record links) reaches only stored digests and
boundary digests; and, when the records have no cycle, it reaches every stored record. -/
theorem RelStore.fetched (c : RelStore) (hac : Acyclic hashSpec c.raw.abs) :
    (∀ d, Reach hashSpec c.raw.abs (headsRel hashSpec c.raw.abs (boundarySet c.boundary)) d →
      d ∈ inView hashSpec c.raw.abs (boundarySet c.boundary)) ∧
    Tight hashSpec c.raw.abs (headsRel hashSpec c.raw.abs (boundarySet c.boundary)) :=
  ⟨c.fetched_model.1, c.fetched_model.2 hac⟩

/-- **Same heads, same records, for stores with a boundary.** Two stores whose heads are equal,
neither with a cycle, and neither holding a record whose digest the other has only as a boundary
digest, hold the same records. Or two records, across the two stores, have the same digest. -/
theorem RelStore.agree (c d : RelStore) (h : c.heads = d.heads)
    (hc : Acyclic hashSpec c.raw.abs) (hd : Acyclic hashSpec d.raw.abs)
    (hcd : ∀ r ∈ c.raw.abs, hashSpec r ∈ boundarySet d.boundary →
      hashSpec r ∈ digests hashSpec d.raw.abs)
    (hdc : ∀ r ∈ d.raw.abs, hashSpec r ∈ boundarySet c.boundary →
      hashSpec r ∈ digests hashSpec c.raw.abs) :
    c.raw.abs = d.raw.abs ∨ CollisionIn hashSpec (c.raw.abs ∪ d.raw.abs) :=
  RelStore.agree_model c d h hc hd hcd hdc

/-- **`accept` on a store with a boundary, in the spec model.** Every result means what
`AcceptRelMeans` says: an accepted record is the spec's `acceptRel` (a link may be a boundary
digest), and any other result leaves the store as it was and gives the reason. -/
theorem RelStore.abs_accept (c : RelStore) (r : Rec) : AcceptRelMeans c r (c.accept r) :=
  RelStore.accept_means c r

/-- **A merged store holds the records of both stores**, and knows exactly the digests (stored or
boundary) that the two stores know. -/
theorem RelStore.abs_merge {c d e : RelStore} (h : c.merge d = .ok e) :
    e.raw.abs = c.raw.abs ∪ d.raw.abs ∧
      inView hashSpec e.raw.abs (boundarySet e.boundary) =
        inView hashSpec c.raw.abs (boundarySet c.boundary) ∪
          inView hashSpec d.raw.abs (boundarySet d.boundary) :=
  RelStore.merge_model h

/-- **`OPEN` of a relative blob, in the spec model.** `load g B u` (what `OPEN` runs on the
records `u` and boundary `B` of a relative blob) gives the store `c` exactly when the boundary is
under its limit, `u` is within the size limits, accept-built relative to `B`, free of collisions
and all of chat `g`; and then `c` is the store of chat `g` over the boundary `B` holding exactly
the records of `u`. -/
theorem RelStore.open_iff {g : GroupId} {B : Boundary} {u : Array Rec} {c : RelStore} :
    RelStore.load g B u = .ok c ↔
      B.size < maxRecords ∧ WellSized u ∧ AcceptBuiltRel hashSpec (boundarySet B) (specOf u) ∧
        ¬ CollisionIn hashSpec (specOf u) ∧ (∀ r ∈ u, r.group = g) ∧ c.raw.abs = specOf u ∧
        c.group = g ∧ c.boundary = B :=
  RelStore.load_iff_model

/-- **`SALVAGE` of a relative blob, in the spec model.** If `salvage g B u` loads `s`, then `u` has
no collision, the store holds exactly what the model's salvage relative to `B` keeps
(`buildRetryRel`), it is of chat `g` over the boundary `B`, and `dropped` is sorted and holds
exactly the digests of the other records of `u`. -/
theorem RelStore.salvage_spec {g : GroupId} {B : Boundary} {u : Array Rec}
    {s : RelStore.Salvaged} (h : RelStore.salvage g B u = .ok s) :
    ¬ CollisionIn hashSpec (specOf u) ∧
      s.store.raw.abs = buildRetryRel hashSpec (boundarySet B) (specOf u) ∧ s.store.group = g ∧
      s.store.boundary = B ∧
      (∀ d, d ∈ s.dropped ↔
        d ∈ digests hashSpec (specOf u \ buildRetryRel hashSpec (boundarySet B) (specOf u))) ∧
      StrictlySorted s.dropped :=
  RelStore.salvage_model h

/-- **A relative store's blob opens as exactly that store** (records, heads, boundary and
vouchers), with the audiences it recorded for its stored records (`storedAudiences`). -/
theorem RelStore.encode_open (c : RelStore) (auds : AudTable) :
    openChat c.group (encodeChat (.relative c) auds) =
      .ok (.relative c, storedAudiences (.relative c) auds) :=
  ChatStore.encode_reopens (.relative c) auds

/-- **Confirmation, with boundaries.** A live message links the digests `hs`, and the sender's
store `d` holds a record for each. Each digest the links reach in your store `c` is reached in
the sender's store too; or your store reaches it from a digest `b` that the sender holds only as a
boundary digest, which the links reach in the sender's store. Or two records, across the two
stores, have the same digest. -/
theorem RelStore.confirmed (c d : RelStore) (hs : Array Digest) (hd : ∀ h ∈ hs, d.has h = true) :
    (∀ x, Reach hashSpec c.raw.abs hs.toList.toFinset x →
      Reach hashSpec d.raw.abs hs.toList.toFinset x ∨
        ∃ b ∈ d.boundaryDigests, Reach hashSpec d.raw.abs hs.toList.toFinset b ∧
          Reach hashSpec c.raw.abs {b} x) ∨
      CollisionIn hashSpec (c.raw.abs ∪ d.raw.abs) :=
  RelStore.confirmed_model c d hs hd

/-- **`CLASSIFY` on a store with a boundary computes the spec's `status`.** For a relative store
without a cycle, `classifyRaw` (what `ChatStore.classify` runs on it) gives digest `d` the status
`st` exactly when `d` is the digest of a stored record `r` and the spec's `status` of `r` is
`st`. -/
theorem RelStore.classify_spec (c : RelStore) (hac : Acyclic hashSpec c.raw.abs)
    (facts : Array Fact) (d : Digest) (st : Zrdt.Status) :
    (classifyRaw c.raw facts)[d]? = some st ↔
      ∃ r, c.get d = some r ∧
        Crdt.Merkle.status hashSpec c.raw.abs (liveOf facts) (toSpec r) = st.toSpec :=
  RelStore.classify_model c hac facts d st

/-- **Same heads, same history, against a store with a boundary** (JOIN_PLAN §6.7, §7.2). The
statement of `CheckedStore.agree_rel` for a responder that is a former newcomer: take a view
(records `F`, boundary digests `B`) with the same heads as the store `c` seen with its own
boundary, holding no record whose digest `c` has only as a boundary digest. Then each digest
reachable from the view's heads is the digest of a record of `c`, and every record of the view
with that digest is in `c`; or a boundary digest of `c` only, for which the view holds no record.
Or two records, across `c` and the view, have the same digest. Nothing is assumed about `B`. -/
theorem RelStore.agree_rel (c : RelStore) {F : SpecStore} {B : Finset Digest}
    (hh : headsRel hashSpec F B = headsRel hashSpec c.raw.abs (boundarySet c.boundary))
    (hFB : ∀ r ∈ F, hashSpec r ∈ boundarySet c.boundary →
      hashSpec r ∈ digests hashSpec c.raw.abs) :
    ∀ d, Reach hashSpec F (headsRel hashSpec F B) d →
      (d ∈ digests hashSpec c.raw.abs ∧ ∀ r ∈ F, hashSpec r = d → r ∈ c.raw.abs) ∨
        (d ∈ boundarySet c.boundary ∧ d ∉ digests hashSpec c.raw.abs ∧
          ∀ r ∈ F, hashSpec r ≠ d) ∨
        CollisionIn hashSpec (c.raw.abs ∪ F) :=
  agree_rel' hashSpec c.built.closedRel hh hFB

/-- **Content goes only where its author sent it, from a store with a boundary** (JOIN_PLAN §7.1;
a former newcomer re-serves). Every opening in `SERVE`'s reply to `q` from the relative store `c`
opens a record of `c`, and that opening's own committed audience seats `q`'s account under the
tag of `q`'s identity key. -/
theorem RelStore.serve_content (c : RelStore) {me : Serve.Me} {held : Serve.HeldMap}
    {q : Serve.Query} {r : Rec} {op : ByteArray} {ac : Bool}
    (he : Serve.Entry.addressed r (some op) ac ∈ Serve.serve c.raw me held q) :
    toSpec r ∈ c.raw.abs ∧ openingMatches r.group r.author r.commit op = true ∧
      ∃ aud, Serve.audienceOf op = some aud ∧ Serve.seats aud q.aci q.key = true := by
  obtain ⟨d, hget, h⟩ := Serve.serve_content he
  exact ⟨((c.get_eq_some_iff).mp hget).1, h op rfl⟩

/-- **Content that may go, goes, from a store with a boundary** (the converse of
`RelStore.serve_content`). Take a record `r` of the relative store `c` and an opening the
responder holds for it that `serveOpening` accepts. If the request is a catch-up whose `since`
does not reach `r`, or a per-digest request that asks for `r`, then the reply carries `r` with
that opening, marked author copy exactly when it is one. -/
theorem RelStore.serve_content_complete (c : RelStore) {me : Serve.Me}
    {held : Serve.HeldMap} {q : Serve.Query} {r : Rec} {op : ByteArray}
    (hr : toSpec r ∈ c.raw.abs) (hop : (held.getD (hashRecord r) {}).opening = some op)
    (hs : Serve.serveOpening me q (hashRecord r) r op = true)
    (hmode : (q.wanted = none ∧
        ¬ Reach hashSpec c.raw.abs (q.since ++ q.ownSince).toList.toFinset (hashRecord r)) ∨
      ∃ ws, q.wanted = some ws ∧ hashRecord r ∈ ws) :
    Serve.Entry.addressed r (some op) (Serve.authorCopy me (hashRecord r) r) ∈
      Serve.serve c.raw me held q := by
  have hget : c.raw.map[hashRecord r]? = some r := (c.get_eq_some_iff).mpr ⟨hr, rfl⟩
  rcases hmode with ⟨hq, hn⟩ | ⟨ws, hq, hw⟩
  · refine Serve.serve_content_complete hget hop hs (by simp [hq]) (.inr ?_)
    rw [Bool.eq_false_iff, ne_eq, Std.ExtTreeSet.contains_iff_mem, Serve.Rel.mem_sinceReach]
    exact fun h => hn h.2
  · exact Serve.serve_content_complete hget hop hs (by simp [hq, hw]) (.inl (by simp [hq]))

/-! ### Part 5 examples

Each statement on a concrete store with every hypothesis discharged: Bob's relative store
`Serve.Rel.Examples.bobRel` (`b1`, `c1`, `a2` accepted over the boundary digest of `a1`), which
has no cycle (`bobRel_acyclic`); and, with the empty boundary, the closed statements of Parts 1
to 3. The rejecting cases are `below_boundary_not_vouched` (`agree` needs `hcd` and `hdc`),
`promoted_cycle_not_tight` (`fetched` needs no cycle), and the two below. -/

open Serve.Rel.Examples in
example : ¬ CollisionIn hashSpec bobRel.raw.abs := RelStore.no_collision _

open Serve.Rel.Examples in
example : (∀ d, Reach hashSpec bobRel.raw.abs
      (headsRel hashSpec bobRel.raw.abs (boundarySet bobRel.boundary)) d →
      d ∈ inView hashSpec bobRel.raw.abs (boundarySet bobRel.boundary)) ∧
    Tight hashSpec bobRel.raw.abs
      (headsRel hashSpec bobRel.raw.abs (boundarySet bobRel.boundary)) :=
  RelStore.fetched _ bobRel_acyclic

-- With the empty boundary, `RelStore.fetched` is `CheckedStore.fetched`.
example (c : CheckedStore) : Fetched hashSpec (abs c) (Crdt.Merkle.heads hashSpec (abs c)) := by
  obtain ⟨h1, h2⟩ := RelStore.fetched (RelStore.ofChecked c) (ReadyStore.ofChecked c).acyclic
  have hb : boundarySet (RelStore.ofChecked c).boundary = ∅ := boundarySet_empty
  have ha : (RelStore.ofChecked c).raw.abs = abs c := rfl
  simp only [hb, ha, headsRel_empty, inView_empty] at h1 h2
  exact ⟨fun d hd => (mem_digests hashSpec).mp (h1 d hd), h2⟩

open Serve.Rel.Examples in
example : bobRel.raw.abs = bobRel.raw.abs ∨
    CollisionIn hashSpec (bobRel.raw.abs ∪ bobRel.raw.abs) :=
  RelStore.agree _ _ rfl bobRel_acyclic bobRel_acyclic
    (fun r hr _ => (mem_digests hashSpec).mpr ⟨r, hr, rfl⟩)
    (fun r hr _ => (mem_digests hashSpec).mpr ⟨r, hr, rfl⟩)

-- With the empty boundary, `RelStore.agree` is `CheckedStore.agree`: Alice's and Bob's stores,
-- built in different orders.
example : abs Examples.aliceStore = abs Examples.bobStore ∨
    CollisionIn hashSpec (abs Examples.aliceStore ∪ abs Examples.bobStore) :=
  RelStore.agree (RelStore.ofChecked Examples.aliceStore) (RelStore.ofChecked Examples.bobStore)
    Examples.aliceStore_heads_eq_bobStore (ReadyStore.ofChecked _).acyclic
    (ReadyStore.ofChecked _).acyclic (fun _ _ h => by simp [RelStore.ofChecked] at h)
    (fun _ _ h => by simp [RelStore.ofChecked] at h)

open Serve.Rel.Examples in
example : AcceptRelMeans bobRel Examples.b1 (bobRel.accept Examples.b1) :=
  RelStore.abs_accept _ _

/-- Merging a store with no records and no boundary into any store succeeds. -/
theorem Examples.relMerge_empty_ok (c : RelStore) :
    ∃ e, c.merge (RelStore.empty c.group) = .ok e := by
  unfold RelStore.merge
  have hg : (RelStore.empty c.group).group = c.group := rfl
  simp only [hg, ne_eq, not_true_eq_false, ↓reduceIte]
  have hb : (RelStore.empty c.group).boundary.toList = [] := by
    simp [RelStore.empty, RelStore.emptyWith]
  rw [hb]
  simp only [RelStore.addBoundaryAll]
  have hr : (RelStore.empty c.group).records = #[] := by
    simp [RelStore.records, RelStore.empty, RelStore.emptyWith]
  rw [hr]
  obtain ⟨-, -, -, -, -, hleft⟩ := RelStore.acceptAll_sound c #[]
  generalize c.acceptAll #[] = res at hleft ⊢
  obtain ⟨e, left⟩ := res
  have hl : left = #[] := by
    rw [Array.eq_empty_iff_forall_not_mem]
    intro x hx
    simpa using hleft x hx
  subst hl
  exact ⟨e, rfl⟩

example (c : RelStore) : ∃ e, c.merge (RelStore.empty c.group) = .ok e ∧
    e.raw.abs = c.raw.abs ∪ (RelStore.empty c.group).raw.abs := by
  obtain ⟨e, he⟩ := Examples.relMerge_empty_ok c
  exact ⟨e, he, (RelStore.abs_merge he).1⟩

-- `open_iff`, forwards, on Bob's store: its records load over its boundary as itself.
open Serve.Rel.Examples in
example : bobRel.boundary.size < maxRecords ∧ WellSized bobRel.records ∧
    AcceptBuiltRel hashSpec (boundarySet bobRel.boundary) (specOf bobRel.records) ∧
    ¬ CollisionIn hashSpec (specOf bobRel.records) ∧
    (∀ r ∈ bobRel.records, r.group = bobRel.group) ∧ bobRel.raw.abs = specOf bobRel.records ∧
    bobRel.group = bobRel.group ∧ bobRel.boundary = bobRel.boundary :=
  RelStore.open_iff.mp (RelStore.load_reopens bobRel)

-- `open_iff` rejects a bad input: `b1` alone (its link, `a1`, neither a record nor a boundary
-- digest) does not load over the empty boundary.
example (c : RelStore) : RelStore.load Examples.group ∅ #[Examples.b1] ≠ .ok c := by
  intro h
  obtain ⟨-, -, hab, -⟩ := RelStore.open_iff.mp h
  rw [boundarySet_empty, acceptBuiltRel_empty_iff] at hab
  exact Examples.b1_alone_not_acceptBuilt hab

-- `salvage_spec` on any relative store's own records and boundary: salvage succeeds and keeps
-- exactly what the model keeps.
example (c : RelStore) : ∃ s, RelStore.salvage c.group c.boundary c.records = .ok s ∧
    s.store.raw.abs = buildRetryRel hashSpec (boundarySet c.boundary) (specOf c.records) := by
  have hw : WellSized c.records := wellSized_values c.built
  obtain ⟨s, hs⟩ := RelStore.salvage_ok_of c.built.boundary_lt hw
    (fun r hr => by obtain ⟨k, hk⟩ := RelStore.mem_records.mp hr; exact c.built.group_eq k r hk)
    (fun x hx y hy hxy => by
      obtain ⟨kx, hkx⟩ := RelStore.mem_records.mp hx
      obtain ⟨ky, hky⟩ := RelStore.mem_records.mp hy
      rw [c.built.hash_eq kx x hkx, c.built.hash_eq ky y hky] at hxy
      subst hxy
      rw [hkx] at hky
      exact Option.some.inj hky)
  exact ⟨s, hs, (RelStore.salvage_spec hs).2.1⟩

open Serve.Rel.Examples in
example : openChat bobRel.group (encodeChat (.relative bobRel) ∅) =
    .ok (.relative bobRel, storedAudiences (.relative bobRel) ∅) :=
  RelStore.encode_open _ _

-- `confirmed` on two closed stores (the empty boundary): a message linking `a1`.
example : (∀ x, Reach hashSpec (abs Examples.s1) (#[hashRecord Examples.a1].toList.toFinset) x →
      Reach hashSpec (abs Examples.s2) (#[hashRecord Examples.a1].toList.toFinset) x ∨
        ∃ b ∈ (RelStore.ofChecked Examples.s2).boundaryDigests,
          Reach hashSpec (abs Examples.s2) (#[hashRecord Examples.a1].toList.toFinset) b ∧
          Reach hashSpec (abs Examples.s1) {b} x) ∨
    CollisionIn hashSpec (abs Examples.s1 ∪ abs Examples.s2) :=
  RelStore.confirmed (RelStore.ofChecked Examples.s1) (RelStore.ofChecked Examples.s2)
    #[hashRecord Examples.a1] (fun h hh => by simp at hh; subst hh; exact Examples.s2_has_a1)

open Serve.Rel.Examples in
example (facts : Array Fact) (d : Digest) (st : Zrdt.Status) :
    (classifyRaw bobRel.raw facts)[d]? = some st ↔
      ∃ r, bobRel.get d = some r ∧
        Crdt.Merkle.status hashSpec bobRel.raw.abs (liveOf facts) (toSpec r) = st.toSpec :=
  RelStore.classify_spec _ bobRel_acyclic _ _ _

-- `CLASSIFY` on a relative store runs `classifyRaw`.
example (c : RelStore) (facts : Array Fact) :
    ChatStore.classify (.relative c) facts = classifyRaw c.raw facts := rfl

/-- Carol's catch-up from Bob, a former newcomer: the reply of `SERVE` for Carol, under her key,
from Bob's relative store, with his `boundaryDigests` as his boundary (as `zrdtd` passes it). -/
def Examples.carolReply : List Serve.Entry :=
  Serve.serve Serve.Rel.Examples.bobRel.raw Serve.Rel.Examples.meBob Serve.Examples.held
    (Serve.Examples.rq Examples.carol Serve.Examples.keyCarol)

example : Examples.carolReply = Serve.serve Serve.Rel.Examples.bobRel.raw
    Serve.Rel.Examples.meBob Serve.Examples.held
    (Serve.Examples.rq Examples.carol Serve.Examples.keyCarol) := rfl

-- `RelStore.agree_rel` on Carol's view after that catch-up, against Bob's relative store (its
-- boundary is not empty): `serve_heads_code` and `replyRecords_subset` discharge the hypotheses.
open Serve.Rel.Examples in
example : ∀ d, Reach hashSpec (Serve.replyRecords Examples.carolReply)
      (headsRel hashSpec (Serve.replyRecords Examples.carolReply)
        (Serve.replyBoundary Examples.carolReply)) d →
    (d ∈ digests hashSpec bobRel.raw.abs ∧
        ∀ r ∈ Serve.replyRecords Examples.carolReply, hashSpec r = d → r ∈ bobRel.raw.abs) ∨
      (d ∈ boundarySet bobRel.boundary ∧ d ∉ digests hashSpec bobRel.raw.abs ∧
        ∀ r ∈ Serve.replyRecords Examples.carolReply, hashSpec r ≠ d) ∨
      CollisionIn hashSpec (bobRel.raw.abs ∪ Serve.replyRecords Examples.carolReply) :=
  bobRel.agree_rel ((Serve.Rel.serve_heads_code _ _ _ _ rfl rfl).trans bobRel.heads_toFinset)
    fun r hr _ => (mem_digests hashSpec).mpr ⟨r, Serve.Rel.replyRecords_subset _ _ _ _ hr, rfl⟩

-- With the empty boundary, `RelStore.agree_rel` is `CheckedStore.agree_rel` with `BS = ∅`.
example (c : CheckedStore) {F : SpecStore} {B : Finset Digest}
    (hh : headsRel hashSpec F B = headsRel hashSpec (abs c) ∅)
    (hFB : ∀ r ∈ F, hashSpec r ∈ (∅ : Finset Digest) → hashSpec r ∈ digests hashSpec (abs c)) :
    ∀ d, Reach hashSpec F (headsRel hashSpec F B) d →
      (d ∈ digests hashSpec (abs c) ∧ ∀ r ∈ F, hashSpec r = d → r ∈ abs c) ∨
        (d ∈ (∅ : Finset Digest) ∧ d ∉ digests hashSpec (abs c) ∧ ∀ r ∈ F, hashSpec r ≠ d) ∨
        CollisionIn hashSpec (abs c ∪ F) := by
  have hb : boundarySet (RelStore.ofChecked c).boundary = ∅ := boundarySet_empty
  have ha : (RelStore.ofChecked c).raw.abs = abs c := rfl
  have := RelStore.agree_rel (RelStore.ofChecked c) (F := F) (B := B)
  rw [hb, ha] at this
  exact this hh hFB

/-- Alice's message to herself, in a store with a boundary: accepted over the boundary digest of
`a1` (`Examples.bnd`), as a newcomer's store would hold it. -/
def Examples.selfRel : RelStore :=
  ((RelStore.emptyWith Examples.group Examples.bnd (by decide)).accept
    Serve.Examples.selfMsg.1).2

/-- Its boundary is not empty: it is `a1`'s digest. -/
theorem Examples.selfRel_boundary : Examples.selfRel.boundary = Examples.bnd := rfl

example : Examples.selfRel.boundary ≠ ∅ := by
  rw [Examples.selfRel_boundary]
  intro h
  have : hashRecord Examples.a1 ∈ Examples.bnd := by simp [Examples.bnd]
  rw [h] at this
  simp at this

/-- The store holds Alice's message under its digest. -/
theorem Examples.selfRel_get :
    Examples.selfRel.get Serve.Examples.selfDigest = some Serve.Examples.selfMsg.1 := by
  have hl : Serve.Examples.selfMsg.1.links = #[] := by decide +kernel
  have hok : (rawAcceptRel (RelStore.emptyWith Examples.group Examples.bnd (by decide)).raw
      Examples.bnd Serve.Examples.selfMsg.1).1 = .accepted Serve.Examples.selfDigest :=
    rawAcceptRel_of_ok (by decide +kernel) (by simp [Rec.WellSized, hl, maxLinks])
      (by simp [hl]) (by simp [RelStore.emptyWith]) (by simp [RelStore.emptyWith, maxRecords])
  have h := rawAcceptRel_accepted
    (c' := (rawAcceptRel (RelStore.emptyWith Examples.group Examples.bnd (by decide)).raw
      Examples.bnd Serve.Examples.selfMsg.1).2) (Prod.ext hok rfl)
  show (rawAcceptRel (RelStore.emptyWith Examples.group Examples.bnd (by decide)).raw
      Examples.bnd Serve.Examples.selfMsg.1).2.map[Serve.Examples.selfDigest]? =
    some Serve.Examples.selfMsg.1
  rw [h.2.2.1]
  exact Std.ExtTreeMap.getElem?_insert_self

/-- **`RelStore.serve_content_complete`, satisfied.** Alice's catch-up from her store with a
boundary carries her message with its opening, as an author copy. -/
theorem Examples.selfRel_served : Serve.Entry.addressed Serve.Examples.selfMsg.1
    (some Serve.Examples.selfMsg.2) true ∈
    Serve.serve Examples.selfRel.raw Serve.Examples.selfMe Serve.Examples.selfHeld
      (Serve.Examples.rq Examples.alice Serve.Examples.keyAlice) := by
  have hac : Serve.authorCopy Serve.Examples.selfMe (hashRecord Serve.Examples.selfMsg.1)
      Serve.Examples.selfMsg.1 = true := by
    have hauth : Serve.Examples.selfMsg.1.author = Examples.alice := by decide +kernel
    simp [Serve.authorCopy, Serve.Examples.selfMe, Serve.Examples.selfDigest, hauth]
  have := Examples.selfRel.serve_content_complete (held := Serve.Examples.selfHeld)
    ((Examples.selfRel.get_eq_some_iff).mp Examples.selfRel_get).1
    (by simp [Serve.Examples.selfHeld, Serve.Examples.selfDigest])
    (Serve.Examples.selfMsg_serveOpening false false)
    (.inl ⟨rfl, by simpa [Serve.Examples.rq] using Examples.not_reach_empty _ _⟩)
  rwa [hac] at this

-- `RelStore.serve_content` applied to that reply.
example : toSpec Serve.Examples.selfMsg.1 ∈ Examples.selfRel.raw.abs ∧
    openingMatches Serve.Examples.selfMsg.1.group Serve.Examples.selfMsg.1.author
      Serve.Examples.selfMsg.1.commit Serve.Examples.selfMsg.2 = true ∧
    ∃ aud, Serve.audienceOf Serve.Examples.selfMsg.2 = some aud ∧
      Serve.seats aud (Serve.Examples.rq Examples.alice Serve.Examples.keyAlice).aci
        (Serve.Examples.rq Examples.alice Serve.Examples.keyAlice).key = true :=
  Examples.selfRel.serve_content Examples.selfRel_served

-- `RelStore.serve_content` rejects a reply from that store that gives Carol the opening of Alice's
-- message to herself: its committed audience seats only Alice.
example : ¬ ∃ aud, Serve.audienceOf Serve.Examples.selfMsg.2 = some aud ∧
    Serve.seats aud Examples.carol Serve.Examples.keyCarol = true := by
  rintro ⟨aud, ha, hs⟩
  have hno : (Serve.audienceOf Serve.Examples.selfMsg.2).any
      (Serve.seats · Examples.carol Serve.Examples.keyCarol) = false := by decide +kernel
  simp [ha, hs] at hno

/-! ## Part 6: the apps (docs/apps/BUILD_M1.md §C)

One section per lane. A lane edits only its own section, between its `BEGIN` and `END` lines. -/

-- [BEGIN lane base] Part 6a: app messages and piece stores (BUILD_M1 §C.1)

-- [END lane base]

-- [BEGIN lane torrent] Part 6b: torrent (BUILD_M1 §C.2)

/-! ### Part 6b: piece stores and the torrent (lane torrent)

The advertised statements of BUILD_M1 §C.4 for lane torrent, in the namespace `Zrdt.Apps`, each a
restatement of a theorem about the shipped code (`core/Zrdt/PieceProofs.lean`) with the collision
spelled out:

* `Apps.assemble_unique`: everyone who completes holds the same bytes. Two streams that pass
  `assembleOk` under contexts bound (`bindCtx`) from announcements with one digest are equal, or
  SHA-256 has a collision.
* `Apps.btBuild_complete`: the author's own announcement makes her file fetchable. Any bind of
  the announcement that `BT_BUILD` built accepts exactly her stream, under the piece digests
  `BT_BUILD` returned.

What they mean depends on, beyond Part 4's list: `bindCtx`, `assembleOk`, `pieceOk`,
`pieceRecord`, `pieceMessage`, `slice`, `pieceLen`, `pieceCount`, `appOf`, `appHeader`,
`Descriptor.parse` (`core/Zrdt/AppBase.lean`) and `btBuild` (`core/Zrdt/Torrent.lean`). -/

/-- **Everyone who completes holds the same bytes** (BUILD_M1 §A.1, §C.2). Two devices bind
announcements with one digest, each with whatever Signal group, app and opening it was given, and
each accepts a stream with `assembleOk` (every slice is the piece the announcement committed for
its index, and the length is L). Then the two streams are equal, or SHA-256 has a collision. -/
theorem Apps.assemble_unique {sg₁ sg₂ : GroupId} {p₁ p₂ o₁ o₂ s₁ s₂ : ByteArray} {A₁ A₂ : Rec}
    {c₁ c₂ : AppBase.PieceCtx} (hA : hashRecord A₁ = hashRecord A₂)
    (h₁ : AppBase.bindCtx sg₁ p₁ A₁ o₁ = .ok c₁) (h₂ : AppBase.bindCtx sg₂ p₂ A₂ o₂ = .ok c₂)
    (hs₁ : AppBase.assembleOk c₁ s₁ = true) (hs₂ : AppBase.assembleOk c₂ s₂ = true) :
    s₁ = s₂ ∨ ∃ x y : ByteArray, x ≠ y ∧ sha256 x = sha256 y :=
  PieceProofs.assemble_unique hA h₁ h₂ hs₁ hs₂

/-- **The author's own announcement makes her file fetchable** (BUILD_M1 §B.6, §C.2). `BT_BUILD`
returned A's committed bytes `msg` and the piece digests `ord` for the stream `s` (channel `ch`,
author `a`, store nonce `nc`, pieces of 2^`e` bytes). Commit `msg` with any nonce `n` and any
links `ls` (A's record), and bind it in any Signal group: the context accepts `s`, and its piece
digests are `ord`. -/
theorem Apps.btBuild_complete {ch sg : GroupId} {a : Aci} {nc n : Nonce} {e : Nat}
    {aud ptrs s msg : ByteArray} {name : String} {ord : Array Digest} {ls : Array Digest}
    {ctx : AppBase.PieceCtx} (hb : Torrent.btBuild ch a nc e aud name ptrs s = .ok (msg, ord))
    (hbind : AppBase.bindCtx sg AppBase.appTorrent
      (Rec.make ch (AppBase.commitOf ch a n msg) ls a) (n.bytes ++ msg) = .ok ctx) :
    AppBase.assembleOk ctx s = true ∧ ctx.desc.ordered = ord :=
  Torrent.btBuild_complete hb hbind

-- [END lane torrent]

-- [BEGIN lane git] Part 6c: git (BUILD_M1 §C.3)

-- [END lane git]

end Zrdt
