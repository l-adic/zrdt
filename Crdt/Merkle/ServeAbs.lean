/-
Copyright (c) 2026 zrdt contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: zrdt contributors
-/
import Mathlib
import Crdt.Merkle.Rel
import Crdt.Merkle.ClassifyFast
import Zrdt.Serve

set_option linter.unusedSectionVars false

/-!
# `SERVE`'s catch-up reply is the spec's served view (docs/JOIN_PLAN.md §7.2, `serve_abs`)

`Zrdt.Serve.serve` (`core/Zrdt/Serve.lean`) is the function `zrdtd` runs when a member asks
another member for its store. `Crdt/Merkle/Rel.lean` says, in the spec model, which view a
responder with records `S` and boundary digests `BS` should serve to a requester who may see the
records `vis`: `servedF` (its records that reach a `vis` record) and `servedB'` (the other digests
of its view that those records link, and its other heads). This file proves that the running code
serves exactly that view.

* `visSpec c held q`: the records `q` may see. A record of the store is in it when the audience
  the responder knows for it seats `q` (`entitledHere`), and it is not reachable from `q`'s
  `since` joined with the responder's own `since` (the spec's `Reach`).
* `serve_abs`: for a catch-up request, the records of the reply's `addressed` entries are exactly
  the records of the store in `visSpec`; the records of its `addressed` and `after` entries are
  exactly `servedF`; and its `boundary` digests are exactly `servedB'`, with the responder's own
  boundary as `BS`. A record whose audience the responder does not hold is never in `visSpec`, so
  it goes as a boundary digest when a served record links it or it is a head.

With `Rel.lean`, for every catch-up reply:

* `serve_heads`: the reply, as a view, has exactly the heads of the responder's view. A newcomer
  who caught up shows the compare code of the member that served him (JOIN_PLAN §6.7).
* `serve_closed`, `serve_tight`: every link of a served record is a served record or a served
  boundary digest, and every served record is reachable from the served heads. So the newcomer
  can accept every served record.
* `serve_boundary_spec`: a served boundary digest is one the responder knows, and from it no
  record `q` may see is reachable. The boundary hides no record `q` may see.

The facts about the responder these need are `CheckedStore.closedRel` and
`CheckedStore.tightRel`: a checked store is closed, and fetched from its heads, relative to any
boundary.

And for every reply, catch-up or per-digest:

* `serve_after_reaches`: an `after` entry is a record of the store from which a record `q` may
  see is reachable (`mem_reachersOf`, JOIN_PLAN §6.4: structure, never content).
* `replyRecords_subset`: the records of a reply are records of the store.

The proofs read the code's walks in the spec's words: `upSet` is the set of digests of
`servedF` (`mem_upSet_of_get`, from `mem_reachersOf` and `mem_walk_iff`), and `sinceReach` is
the spec's `Reach` from `since` (`mem_sinceReach`, from `walkReach_iff`).
-/

namespace Zrdt
namespace Serve

open Crdt.Merkle

/-! ## The reply as a view -/

/-- The records of a reply's `addressed` entries (the records sent to the requester), as spec
records. -/
def replyAddressed (es : List Entry) : SpecStore :=
  (es.filterMap fun
    | .addressed r _ _ => some (toSpec r)
    | _ => none).toFinset

example : replyAddressed [.boundary (Zrdt.Examples.dig 1)] = ∅ := rfl

/-- The records of a reply's `addressed` and `after` entries, as spec records: the full records
of the view the requester gets. -/
def replyRecords (es : List Entry) : SpecStore :=
  (es.filterMap fun
    | .addressed r _ _ => some (toSpec r)
    | .after r => some (toSpec r)
    | .boundary _ => none).toFinset

example : replyRecords [.boundary (Zrdt.Examples.dig 1)] = ∅ := rfl

/-- The digests of a reply's `boundary` entries: the boundary of the view the requester gets. -/
def replyBoundary (es : List Entry) : Finset Digest :=
  (es.filterMap fun
    | .boundary d => some d
    | _ => none).toFinset

example : replyBoundary [.boundary (Zrdt.Examples.dig 1)] = {Zrdt.Examples.dig 1} := rfl

/-- A record is in `replyAddressed` exactly when an `addressed` entry carries it. -/
theorem mem_replyAddressed {es : List Entry} {x : SpecRec} :
    x ∈ replyAddressed es ↔ ∃ r, (∃ o ac, Entry.addressed r o ac ∈ es) ∧ toSpec r = x := by
  simp only [replyAddressed, List.mem_toFinset, List.mem_filterMap]
  constructor
  · rintro ⟨e, he, hx⟩
    cases e with
    | addressed r o ac => exact ⟨r, ⟨o, ac, he⟩, Option.some.inj hx⟩
    | after r => simp at hx
    | boundary d => simp at hx
  · rintro ⟨r, ⟨o, ac, he⟩, rfl⟩
    exact ⟨_, he, rfl⟩

/-- A record is in `replyRecords` exactly when an `addressed` or an `after` entry carries it. -/
theorem mem_replyRecords {es : List Entry} {x : SpecRec} :
    x ∈ replyRecords es ↔
      ∃ r, ((∃ o ac, Entry.addressed r o ac ∈ es) ∨ Entry.after r ∈ es) ∧ toSpec r = x := by
  simp only [replyRecords, List.mem_toFinset, List.mem_filterMap]
  constructor
  · rintro ⟨e, he, hx⟩
    cases e with
    | addressed r o ac => exact ⟨r, .inl ⟨o, ac, he⟩, Option.some.inj hx⟩
    | after r => exact ⟨r, .inr he, Option.some.inj hx⟩
    | boundary d => simp at hx
  · rintro ⟨r, ⟨o, ac, he⟩ | he, rfl⟩
    · exact ⟨_, he, rfl⟩
    · exact ⟨_, he, rfl⟩

/-- A digest is in `replyBoundary` exactly when a `boundary` entry carries it. -/
theorem mem_replyBoundary {es : List Entry} {d : Digest} :
    d ∈ replyBoundary es ↔ Entry.boundary d ∈ es := by
  simp only [replyBoundary, List.mem_toFinset, List.mem_filterMap]
  constructor
  · rintro ⟨e, he, hx⟩
    cases e with
    | addressed r o ac => simp at hx
    | after r => simp at hx
    | boundary d' => cases hx; exact he
  · intro he
    exact ⟨_, he, rfl⟩

/-! ## What the requester may see -/

/-- The records the requester `q` may see (JOIN_PLAN §5's `vis`): the audience the responder
knows for the record seats `q` (`entitledHere`: from a matching held opening, else the audience
`zrdtd` recorded), and the record is not reachable from `q`'s `since` joined with the responder's
own `since` for that account. -/
def visSpec (c : CheckedStore) (held : HeldMap) (q : Query) (x : SpecRec) : Prop :=
  entitledHere held q (hashSpec x) (ofSpec x) = true ∧
    ¬ Reach hashSpec (abs c) (q.since ++ q.ownSince).toList.toFinset (hashSpec x)

/-- `visSpec` is decidable: `Reach` on a finite store is. -/
instance (c : CheckedStore) (held : HeldMap) (q : Query) : DecidablePred (visSpec c held q) :=
  fun _ => by unfold visSpec; infer_instance

-- A responder that holds no opening and no audience knows of no record that `q` may see.
example (c : CheckedStore) (q : Query) (x : SpecRec) : ¬ visSpec c ∅ q x := by
  simp [visSpec, entitledHere, audienceFor]

/-- The responder's own boundary, as a finite set. -/
def boundarySpec (me : Me) : Finset Digest := me.boundary.toList.toFinset

-- A store `zrdtd` holds is closed: its boundary is empty.
example : boundarySpec { aci := Zrdt.Examples.alice } = ∅ := rfl

/-- A digest is in `boundarySpec me` exactly when it is in the responder's boundary. -/
theorem mem_boundarySpec {me : Me} {d : Digest} : d ∈ boundarySpec me ↔ d ∈ me.boundary := by
  rw [boundarySpec, List.mem_toFinset, Std.ExtTreeSet.mem_toList]

/-! ## The walks, in the spec's words -/

/-- `Serve.linkedByMap` is `linkedBy` of `core/Zrdt/Provenance.lean`: the same fold. -/
theorem linkedByMap_eq (c : CheckedStore) : linkedByMap c = linkedBy c := rfl

/-- Reaching from a list of start digests is reaching from one of them. -/
theorem walkReach_iff_exists {β : Type} {m : Std.ExtTreeMap Digest β compare}
    {next : β → List Digest} {L : List Digest} {x : Digest} :
    WalkReach m next L x ↔ ∃ v ∈ L, WalkReach m next [v] x := by
  constructor
  · intro h
    induction h with
    | start hd => exact ⟨_, hd, .start List.mem_cons_self⟩
    | step _ hk hd ih =>
      obtain ⟨v, hv, h⟩ := ih
      exact ⟨v, hv, .step h hk hd⟩
  · rintro ⟨v, hv, h⟩
    induction h with
    | start hd => rw [List.mem_singleton] at hd; subst hd; exact .start hv
    | step _ hk hd ih => exact .step ih hk hd

/-- **The backward walk, in the spec's words.** Walking `linkedBy` from the digests `L` finds
exactly the stored records from which one of `L` is reachable. -/
theorem mem_walk_linkedBy (c : CheckedStore) (L : List Digest) {x : Digest} :
    x ∈ walk id (linkedBy c) ∅ L ↔ x ∈ c.raw.map ∧ ∃ v ∈ L, Reach hashSpec (abs c) {x} v := by
  rw [mem_walk_iff, mem_linkedBy, walkReach_iff_exists]
  refine and_congr_right fun hx => exists_congr fun v => and_congr_right fun _ => ?_
  have h := mem_reachersOf c (d := v) (x := x)
  rw [reachersOf, mem_walk_iff, mem_linkedBy] at h
  exact ⟨fun hw => (h.mp ⟨hx, hw⟩).2, fun hr => (h.mpr ⟨hx, hr⟩).2⟩

/-- `sinceReach` is the spec's reachability from `since` joined with the responder's own. -/
theorem mem_sinceReach {c : CheckedStore} {q : Query} {d : Digest} :
    d ∈ sinceReach c q ↔
      d ∈ c.raw.map ∧ Reach hashSpec (abs c) (q.since ++ q.ownSince).toList.toFinset d := by
  rw [sinceReach, CheckedStore.reachSet, mem_walk_iff, CheckedStore.walkReach_iff]

/-- `visList` lists the stored records that `entitledHere` seats `q` in and that `since` does not
reach. -/
theorem mem_visList {c : CheckedStore} {held : HeldMap} {q : Query} {v : Digest} :
    v ∈ visList c held q ↔
      ∃ r, c.get v = some r ∧ entitledHere held q v r = true ∧ v ∉ sinceReach c q := by
  simp only [visList, List.mem_filterMap, Option.ite_none_right_eq_some, Bool.and_eq_true,
    Bool.not_eq_true', Prod.exists, Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some,
    Bool.eq_false_iff, ne_eq, Std.ExtTreeSet.contains_iff_mem, Option.some.injEq]
  constructor
  · rintro ⟨a, b, hget, ⟨he, hs⟩, rfl⟩
    exact ⟨b, hget, he, hs⟩
  · rintro ⟨r, hget, he, hs⟩
    exact ⟨v, r, hget, ⟨he, hs⟩, rfl⟩

/-- `upSet` holds the stored records from which a `visList` record is reachable. -/
theorem mem_upSet {c : CheckedStore} {held : HeldMap} {q : Query} {d : Digest} :
    d ∈ upSet c held q ↔
      d ∈ c.raw.map ∧ ∃ v ∈ visList c held q, Reach hashSpec (abs c) {d} v :=
  mem_walk_linkedBy c _

/-- `Serve.linksOf c ds` holds the links of the stored records among `ds`. -/
theorem mem_linksOf_code {c : CheckedStore} {ds : List Digest} {d : Digest} :
    d ∈ Serve.linksOf c ds ↔ ∃ k ∈ ds, ∃ r, c.get k = some r ∧ d ∈ r.links := by
  have key : ∀ (ds : List Digest) (acc : DigestSet),
      d ∈ ds.foldl (fun acc d => match c.get d with
        | some r => r.links.foldl (fun s l => s.insert l) acc
        | none => acc) acc ↔ d ∈ acc ∨ ∃ k ∈ ds, ∃ r, c.get k = some r ∧ d ∈ r.links := by
    intro ds
    induction ds with
    | nil => intro acc; simp
    | cons k ds ih =>
      intro acc
      rw [List.foldl_cons, ih]
      cases hk : c.get k with
      | none =>
        dsimp only
        constructor
        · rintro (h | ⟨k', hk', r, hr, hd⟩)
          · exact .inl h
          · exact .inr ⟨k', List.mem_cons_of_mem _ hk', r, hr, hd⟩
        · rintro (h | ⟨k', hk', r, hr, hd⟩)
          · exact .inl h
          · rcases List.mem_cons.mp hk' with rfl | hk'
            · rw [hk] at hr; cases hr
            · exact .inr ⟨k', hk', r, hr, hd⟩
      | some r =>
        dsimp only
        rw [← Array.foldl_toList, mem_foldl_insert]
        constructor
        · rintro ((h | h) | ⟨k', hk', r', hr', hd⟩)
          · exact .inl h
          · exact .inr ⟨k, List.mem_cons_self, r, hk, Array.mem_toList_iff.mp h⟩
          · exact .inr ⟨k', List.mem_cons_of_mem _ hk', r', hr', hd⟩
        · rintro (h | ⟨k', hk', r', hr', hd⟩)
          · exact .inl (.inl h)
          · rcases List.mem_cons.mp hk' with rfl | hk'
            · rw [hk] at hr'; cases hr'
              exact .inl (.inr (Array.mem_toList_iff.mpr hd))
            · exact .inr ⟨k', hk', r', hr', hd⟩
  exact (key ds ∅).trans (by simp)

/-- When a digest that is neither `addressed` nor `after` goes as a boundary digest in a catch-up:
a record of the walk links it, or no stored record links it (it is a head). -/
def boundaryCond (c : CheckedStore) (held : HeldMap) (q : Query) (d : Digest) : Prop :=
  d ∈ Serve.linksOf c (upSet c held q).toList ∨
    d ∉ Serve.linksOf c (c.raw.map.toList.map (·.1))

-- In the empty store nothing links anything, so every digest meets the condition.
example (g : GroupId) (held : HeldMap) (q : Query) (d : Digest) :
    boundaryCond (CheckedStore.empty g) held q d :=
  .inr fun h => by
    obtain ⟨k, hk, -⟩ := mem_linksOf_code.mp h
    simp [CheckedStore.empty] at hk

/-- **The entries of a catch-up reply**, one case per line of JOIN_PLAN §5's table: each stored
record gives an `addressed` entry when `q` may see it, else an `after` entry when it is in the
walk, else a `boundary` entry when `boundaryCond` holds; each digest of the responder's own
boundary that the store does not hold gives a `boundary` entry when `boundaryCond` holds. -/
theorem mem_serve_catchup {c : CheckedStore} {me : Me} {held : HeldMap} {q : Query}
    (hq : q.wanted = none) {e : Entry} :
    e ∈ serve c me held q ↔
      (∃ d r, c.get d = some r ∧
        ((entitledHere held q d r = true ∧ d ∉ sinceReach c q ∧
            e = .addressed r ((held.getD d {}).opening.filter (serveOpening me q d r))
              (authorCopy me d r)) ∨
          (¬ (entitledHere held q d r = true ∧ d ∉ sinceReach c q) ∧ d ∈ upSet c held q ∧
            e = .after r) ∨
          (¬ (entitledHere held q d r = true ∧ d ∉ sinceReach c q) ∧ d ∉ upSet c held q ∧
            boundaryCond c held q d ∧ e = .boundary d))) ∨
      (∃ d, d ∈ me.boundary ∧ d ∉ c.raw.map ∧ boundaryCond c held q d ∧ e = .boundary d) := by
  simp only [serve, hq, List.mem_append, List.mem_filterMap, Option.map_none, Option.getD_none,
    Option.isSome_none, Bool.not_true, Bool.false_eq_true, ite_false, Bool.false_or,
    Bool.true_and, Prod.exists, Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some,
    Std.ExtTreeSet.mem_toList, boundaryCond, Bool.and_eq_true, Bool.or_eq_true,
    Bool.not_eq_true', Bool.eq_false_iff, Std.ExtTreeSet.contains_iff_mem,
    Std.ExtTreeMap.contains_iff_mem, ne_eq]
  constructor
  · rintro (⟨d, r, hget, hf⟩ | ⟨d, hb, hf⟩)
    · refine .inl ⟨d, r, hget, ?_⟩
      split_ifs at hf with h1 h2 h3
      · cases hf; exact .inl ⟨h1.1, h1.2, rfl⟩
      · cases hf; exact .inr (.inl ⟨h1, h2, rfl⟩)
      · cases hf; exact .inr (.inr ⟨h1, h2, h3, rfl⟩)
    · refine .inr ⟨d, hb, ?_⟩
      split_ifs at hf with h1
      cases hf; exact ⟨h1.1, h1.2, rfl⟩
  · rintro (⟨d, r, hget, ⟨h1, h2, rfl⟩ | ⟨h1, h2, rfl⟩ | ⟨h1, h2, h3, rfl⟩⟩ | ⟨d, hb, h1, h2, rfl⟩)
    · exact .inl ⟨d, r, hget, by rw [ite_eq_left ⟨h1, h2⟩]⟩
    · exact .inl ⟨d, r, hget, by rw [ite_eq_right h1, ite_eq_left h2]⟩
    · exact .inl ⟨d, r, hget, by rw [ite_eq_right h1, ite_eq_right h2, ite_eq_left h3]⟩
    · exact .inr ⟨d, hb, by rw [ite_eq_left ⟨h1, h2⟩]⟩

/-! ## Each kind of entry -/

/-- A stored record is stored under its own digest. -/
theorem hash_of_get {c : CheckedStore} {d : Digest} {r : Rec} (h : c.get d = some r) :
    hashRecord r = d :=
  ((c.get_eq_some_iff).mp h).2

/-- A digest `get` finds is a key of the map. -/
theorem mem_map_of_get {c : CheckedStore} {d : Digest} {r : Rec} (h : c.get d = some r) :
    d ∈ c.raw.map :=
  Std.ExtTreeMap.mem_iff_isSome_getElem?.mpr (by rw [show c.raw.map[d]? = c.get d from rfl, h]; rfl)

/-- `visSpec` of a shipped record, in the code's words. -/
theorem visSpec_toSpec {c : CheckedStore} {held : HeldMap} {q : Query} {r : Rec} :
    visSpec c held q (toSpec r) ↔ entitledHere held q (hashRecord r) r = true ∧
      ¬ Reach hashSpec (abs c) (q.since ++ q.ownSince).toList.toFinset (hashRecord r) := by
  simp only [visSpec, hashSpec_toSpec, ofSpec_toSpec]

/-- `visSpec` of a stored record is the test `serve` makes: `entitledHere`, and `since` does not
reach it. -/
theorem visSpec_of_get {c : CheckedStore} {held : HeldMap} {q : Query} {d : Digest} {r : Rec}
    (h : c.get d = some r) :
    visSpec c held q (toSpec r) ↔ entitledHere held q d r = true ∧ d ∉ sinceReach c q := by
  rw [visSpec_toSpec, hash_of_get h, mem_sinceReach]
  exact and_congr_right fun _ => ⟨fun hn hm => hn hm.2, fun hn hR => hn ⟨mem_map_of_get h, hR⟩⟩

/-- `visList` lists the digests of the records in `visSpec`. -/
theorem mem_visList_spec {c : CheckedStore} {held : HeldMap} {q : Query} {v : Digest} :
    v ∈ visList c held q ↔ ∃ t ∈ abs c, visSpec c held q t ∧ hashSpec t = v := by
  rw [mem_visList]
  constructor
  · rintro ⟨r, hget, hv⟩
    exact ⟨toSpec r, ((c.get_eq_some_iff).mp hget).1, (visSpec_of_get hget).mpr hv,
      by rw [hashSpec_toSpec, hash_of_get hget]⟩
  · rintro ⟨t, ht, hv, rfl⟩
    obtain ⟨r, rfl, hr⟩ := c.built.exists_of_mem_abs ht
    rw [hashSpec_toSpec]
    exact ⟨r, hr, (visSpec_of_get hr).mp hv⟩

/-- **`upSet` is `servedF`.** A stored record is in the code's walk exactly when it is in the
spec's `servedF`. -/
theorem mem_upSet_of_get {c : CheckedStore} {held : HeldMap} {q : Query} {d : Digest} {r : Rec}
    (h : c.get d = some r) :
    d ∈ upSet c held q ↔ toSpec r ∈ servedF hashSpec (abs c) (visSpec c held q) := by
  rw [mem_upSet, mem_servedF, hashSpec_toSpec, hash_of_get h]
  simp only [mem_visList_spec]
  constructor
  · rintro ⟨-, v, ⟨t, ht, hv, rfl⟩, hR⟩
    exact ⟨((c.get_eq_some_iff).mp h).1, t, ht, hv, hR⟩
  · rintro ⟨-, t, ht, hv, hR⟩
    exact ⟨mem_map_of_get h, _, ⟨t, ht, hv, rfl⟩, hR⟩

/-- The records of `servedF` are the stored records in `upSet`. -/
theorem mem_servedF_iff {c : CheckedStore} {held : HeldMap} {q : Query} {x : SpecRec} :
    x ∈ servedF hashSpec (abs c) (visSpec c held q) ↔
      ∃ d r, c.get d = some r ∧ d ∈ upSet c held q ∧ toSpec r = x := by
  constructor
  · intro hx
    obtain ⟨r, rfl, hr⟩ := c.built.exists_of_mem_abs (servedF_subset hashSpec _ _ hx)
    exact ⟨_, r, hr, (mem_upSet_of_get hr).mpr hx, rfl⟩
  · rintro ⟨d, r, hr, hu, rfl⟩
    exact (mem_upSet_of_get hr).mp hu

/-- `upSet` holds only stored digests. -/
theorem upSet_subset {c : CheckedStore} {held : HeldMap} {q : Query} {d : Digest}
    (h : d ∈ upSet c held q) : d ∈ c.raw.map :=
  (mem_upSet.mp h).1

/-- The digests of `servedF` are `upSet`. -/
theorem mem_digests_servedF {c : CheckedStore} {held : HeldMap} {q : Query} {d : Digest} :
    d ∈ digests hashSpec (servedF hashSpec (abs c) (visSpec c held q)) ↔ d ∈ upSet c held q := by
  rw [mem_digests]
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨d', r, hr, hu, rfl⟩ := mem_servedF_iff.mp hx
    rwa [hashSpec_toSpec, hash_of_get hr]
  · intro hu
    obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp
      (Std.ExtTreeMap.mem_iff_isSome_getElem?.mp (upSet_subset hu))
    exact ⟨toSpec r, (mem_upSet_of_get hr).mp hu, by rw [hashSpec_toSpec, hash_of_get hr]⟩

/-- The links of `servedF` are what `serve` computes as `linkedByUp`. -/
theorem mem_linksOf_servedF {c : CheckedStore} {held : HeldMap} {q : Query} {d : Digest} :
    d ∈ Crdt.Merkle.linksOf (servedF hashSpec (abs c) (visSpec c held q)) ↔
      d ∈ Serve.linksOf c (upSet c held q).toList := by
  rw [mem_linksOf, mem_linksOf_code]
  constructor
  · rintro ⟨x, hx, hd⟩
    obtain ⟨k, r, hr, hu, rfl⟩ := mem_servedF_iff.mp hx
    exact ⟨k, Std.ExtTreeSet.mem_toList.mpr hu, r, hr, mem_toSpec_links.mp hd⟩
  · rintro ⟨k, hk, r, hr, hd⟩
    exact ⟨toSpec r, mem_servedF_iff.mpr ⟨k, r, hr, Std.ExtTreeSet.mem_toList.mp hk, rfl⟩,
      mem_toSpec_links.mpr hd⟩

/-- The links of the store are what `serve` computes as `linkedAny`. -/
theorem mem_linksOf_abs {c : CheckedStore} {d : Digest} :
    d ∈ Crdt.Merkle.linksOf (abs c) ↔ d ∈ Serve.linksOf c (c.raw.map.toList.map (·.1)) := by
  rw [mem_linksOf, mem_linksOf_code]
  constructor
  · rintro ⟨x, hx, hd⟩
    obtain ⟨r, rfl, hr⟩ := c.built.exists_of_mem_abs hx
    exact ⟨_, List.mem_map.mpr ⟨(hashRecord r, r),
      Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some.mpr hr, rfl⟩, r, hr, mem_toSpec_links.mp hd⟩
  · rintro ⟨k, hk, r, hr, hd⟩
    exact ⟨toSpec r, ((c.get_eq_some_iff).mp hr).1, mem_toSpec_links.mpr hd⟩

/-- A record `q` may see is in the walk (the walk starts at it). -/
theorem mem_upSet_of_vis {c : CheckedStore} {held : HeldMap} {q : Query} {d : Digest} {r : Rec}
    (h : c.get d = some r) (hv : entitledHere held q d r = true ∧ d ∉ sinceReach c q) :
    d ∈ upSet c held q :=
  mem_upSet.mpr ⟨mem_map_of_get h, d, mem_visList.mpr ⟨r, h, hv⟩, .head (Finset.mem_singleton_self _)⟩

/-- In a catch-up, a record goes `addressed` exactly when `q` may see it. -/
theorem addressed_mem_serve {c : CheckedStore} {me : Me} {held : HeldMap} {q : Query}
    (hq : q.wanted = none) {r : Rec} :
    (∃ o ac, Entry.addressed r o ac ∈ serve c me held q) ↔
      ∃ d, c.get d = some r ∧ entitledHere held q d r = true ∧ d ∉ sinceReach c q := by
  constructor
  · rintro ⟨o, ac, he⟩
    rcases (mem_serve_catchup hq).mp he with
      ⟨d, r', hr, ⟨h1, h2, he'⟩ | ⟨-, -, he'⟩ | ⟨-, -, -, he'⟩⟩ | ⟨d, -, -, -, he'⟩
    · cases he'; exact ⟨d, hr, h1, h2⟩
    · cases he'
    · cases he'
    · cases he'
  · rintro ⟨d, hr, h1, h2⟩
    exact ⟨_, _, (mem_serve_catchup hq).mpr (.inl ⟨d, r, hr, .inl ⟨h1, h2, rfl⟩⟩)⟩

/-- In a catch-up, a record goes `after` exactly when `q` may not see it and it is in the walk. -/
theorem after_mem_serve {c : CheckedStore} {me : Me} {held : HeldMap} {q : Query}
    (hq : q.wanted = none) {r : Rec} :
    Entry.after r ∈ serve c me held q ↔
      ∃ d, c.get d = some r ∧ ¬ (entitledHere held q d r = true ∧ d ∉ sinceReach c q) ∧
        d ∈ upSet c held q := by
  constructor
  · intro he
    rcases (mem_serve_catchup hq).mp he with
      ⟨d, r', hr, ⟨-, -, he'⟩ | ⟨h1, h2, he'⟩ | ⟨-, -, -, he'⟩⟩ | ⟨d, -, -, -, he'⟩
    · cases he'
    · cases he'; exact ⟨d, hr, h1, h2⟩
    · cases he'
    · cases he'
  · rintro ⟨d, hr, h1, h2⟩
    exact (mem_serve_catchup hq).mpr (.inl ⟨d, r, hr, .inr (.inl ⟨h1, h2, rfl⟩)⟩)

/-- In a catch-up, a digest goes as a boundary digest exactly when the responder's view knows it
(a stored record or its own boundary), it is not in the walk, and `boundaryCond` holds. -/
theorem boundary_mem_serve {c : CheckedStore} {me : Me} {held : HeldMap} {q : Query}
    (hq : q.wanted = none) {d : Digest} :
    Entry.boundary d ∈ serve c me held q ↔
      (d ∈ c.raw.map ∨ d ∈ me.boundary) ∧ d ∉ upSet c held q ∧ boundaryCond c held q d := by
  constructor
  · intro he
    rcases (mem_serve_catchup hq).mp he with
      ⟨d', r, hr, ⟨-, -, he'⟩ | ⟨-, -, he'⟩ | ⟨-, h2, h3, he'⟩⟩ | ⟨d', hb, hm, h3, he'⟩
    · cases he'
    · cases he'
    · cases he'; exact ⟨.inl (mem_map_of_get hr), h2, h3⟩
    · cases he'; exact ⟨.inr hb, fun hu => hm (upSet_subset hu), h3⟩
  · rintro ⟨hdb, hu, h3⟩
    by_cases hm : d ∈ c.raw.map
    · obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp (Std.ExtTreeMap.mem_iff_isSome_getElem?.mp hm)
      exact (mem_serve_catchup hq).mpr (.inl ⟨d, r, hr,
        .inr (.inr ⟨fun hv => hu (mem_upSet_of_vis hr hv), hu, h3, rfl⟩)⟩)
    · exact (mem_serve_catchup hq).mpr (.inr ⟨d, hdb.resolve_left hm, hm, h3, rfl⟩)

/-! ## The bridge -/

/-- **`SERVE`'s catch-up reply is the spec's served view** (JOIN_PLAN §7.2). For a catch-up
request (`q.wanted = none`):

* the records of the `addressed` entries are exactly the records of the store that `q` may see
  (`visSpec`: seated in the audience the responder knows, and not reachable from `since`);
* the records of the `addressed` and `after` entries are exactly `servedF` for `visSpec`;
* the boundary digests are exactly `servedB'` for `visSpec`, with the responder's own boundary.

Which `addressed` entries carry an opening is `serve_content` and `serve_content_complete`
(`core/Zrdt/Serve.lean`). -/
theorem serve_abs (c : CheckedStore) (me : Me) (held : HeldMap) (q : Query)
    (hq : q.wanted = none) :
    replyAddressed (serve c me held q) = (abs c).filter (visSpec c held q) ∧
      replyRecords (serve c me held q) = servedF hashSpec (abs c) (visSpec c held q) ∧
      replyBoundary (serve c me held q) =
        servedB' hashSpec (abs c) (visSpec c held q) (boundarySpec me) := by
  refine ⟨?_, ?_, ?_⟩
  · ext x
    rw [mem_replyAddressed, Finset.mem_filter]
    simp only [addressed_mem_serve hq]
    constructor
    · rintro ⟨r, ⟨d, hr, hv⟩, rfl⟩
      exact ⟨((c.get_eq_some_iff).mp hr).1, (visSpec_of_get hr).mpr hv⟩
    · rintro ⟨hx, hv⟩
      obtain ⟨r, rfl, hr⟩ := c.built.exists_of_mem_abs hx
      exact ⟨r, ⟨_, hr, (visSpec_of_get hr).mp hv⟩, rfl⟩
  · ext x
    rw [mem_replyRecords, mem_servedF_iff]
    simp only [addressed_mem_serve hq, after_mem_serve hq]
    constructor
    · rintro ⟨r, ⟨d, hr, hv⟩ | ⟨d, hr, -, hu⟩, rfl⟩
      · exact ⟨d, r, hr, mem_upSet_of_vis hr hv, rfl⟩
      · exact ⟨d, r, hr, hu, rfl⟩
    · rintro ⟨d, r, hr, hu, rfl⟩
      by_cases hv : entitledHere held q d r = true ∧ d ∉ sinceReach c q
      · exact ⟨r, .inl ⟨d, hr, hv⟩, rfl⟩
      · exact ⟨r, .inr ⟨d, hr, hv, hu⟩, rfl⟩
  · ext d
    rw [mem_replyBoundary, boundary_mem_serve hq, mem_servedB', mem_inView, mem_digests_servedF,
      mem_linksOf_servedF, mem_linksOf_abs, mem_boundarySpec, boundaryCond]
    have hm : (∃ r ∈ abs c, hashSpec r = d) ↔ d ∈ c.raw.map := by
      rw [← mem_digests, CheckedStore.mem_digests_abs]
    rw [hm]

-- On the store of the examples of `core/Zrdt/Serve.lean`: Bob's catch-up from Alice.
example : replyRecords (serve Examples.store Examples.meAlice Examples.held
      (Examples.rq Zrdt.Examples.bob Examples.keyBob)) =
    servedF hashSpec (abs Examples.store)
      (visSpec Examples.store Examples.held (Examples.rq Zrdt.Examples.bob Examples.keyBob)) :=
  (serve_abs _ _ _ _ rfl).2.1

/-- The records of any reply are records of the store. -/
theorem replyRecords_subset (c : CheckedStore) (me : Me) (held : HeldMap) (q : Query) :
    replyRecords (serve c me held q) ⊆ abs c := by
  intro x hx
  obtain ⟨r, ⟨o, ac, he⟩ | he, rfl⟩ := mem_replyRecords.mp hx
  · obtain ⟨d, hget, -⟩ := serve_addressed he
    exact ((c.get_eq_some_iff).mp hget).1
  · obtain ⟨d, hget, -⟩ := serve_after he
    exact ((c.get_eq_some_iff).mp hget).1

end Serve

namespace CheckedStore

open Crdt.Merkle

/-- A checked store is closed relative to any boundary: every link of a stored record is the
digest of a stored record (`closed`). -/
theorem closedRel (c : CheckedStore) (BS : Finset Digest) : ClosedRel hashSpec (abs c) BS :=
  fun r hr _ hd => (mem_inView hashSpec).mpr (.inl (c.closed r hr _ hd))

example : ClosedRel hashSpec (abs Examples.s1) ∅ := Examples.s1.closedRel ∅

/-- Every record of a checked store is reachable from its heads relative to any boundary: those
heads include its own heads (`fetched`). -/
theorem tightRel (c : CheckedStore) (BS : Finset Digest) :
    Tight hashSpec (abs c) (headsRel hashSpec (abs c) BS) := by
  have ht : Tight hashSpec (abs c) (Crdt.Merkle.heads hashSpec (abs c)) :=
    ((fetched_build hashSpec c.acceptBuilt).resolve_right c.built.no_collision).2
  intro r hr
  refine (ht r hr).lift hashSpec subset_rfl fun d hd => .head ?_
  rw [← headsRel_empty] at hd
  rw [mem_headsRel] at hd ⊢
  refine ⟨?_, hd.2⟩
  rcases (mem_inView hashSpec).mp hd.1 with h | h
  · exact (mem_inView hashSpec).mpr (.inl h)
  · exact absurd h (Finset.notMem_empty d)

example : Tight hashSpec (abs Examples.s1) (headsRel hashSpec (abs Examples.s1) ∅) :=
  Examples.s1.tightRel ∅

end CheckedStore

namespace Serve

open Crdt.Merkle

/-! ## What the newcomer's view is -/

/-- **A newcomer who caught up has the responder's heads** (JOIN_PLAN §6.7). The view of a
catch-up reply (its `addressed` and `after` records, and its boundary digests) has exactly the
heads of the responder's view: its store and its own boundary. No collision clause. -/
theorem serve_heads (c : CheckedStore) (me : Me) (held : HeldMap) (q : Query)
    (hq : q.wanted = none) :
    headsRel hashSpec (replyRecords (serve c me held q)) (replyBoundary (serve c me held q)) =
      headsRel hashSpec (abs c) (boundarySpec me) := by
  obtain ⟨-, hF, hB⟩ := serve_abs c me held q hq
  rw [hF, hB]
  exact served_heads' hashSpec _ _ _

example : headsRel hashSpec
      (replyRecords (serve Examples.store Examples.meAlice Examples.held
        (Examples.rq Zrdt.Examples.bob Examples.keyBob)))
      (replyBoundary (serve Examples.store Examples.meAlice Examples.held
        (Examples.rq Zrdt.Examples.bob Examples.keyBob))) =
    headsRel hashSpec (abs Examples.store) (boundarySpec Examples.meAlice) :=
  serve_heads _ _ _ _ rfl

/-- **Rejecting:** a reply with no entries to Alice's catch-up from `selfStore` would not have
the responder's heads; `serve_heads` rules it out. -/
example : headsRel hashSpec (replyRecords []) (replyBoundary []) ≠
    headsRel hashSpec (abs Examples.selfStore) (boundarySpec Examples.selfMe) := by
  intro h
  have hc : Examples.selfStore.heads.contains Examples.selfDigest = true := by decide +kernel
  have hd : Examples.selfDigest ∈
      headsRel hashSpec (abs Examples.selfStore) (boundarySpec Examples.selfMe) := by
    rw [show boundarySpec Examples.selfMe = ∅ from rfl, headsRel_empty,
      ← CheckedStore.mem_heads_iff]
    exact Std.ExtTreeSet.contains_iff_mem.mp hc
  rw [← h] at hd
  simp [replyRecords, replyBoundary, mem_headsRel, inView, digests] at hd

/-- **The newcomer can accept every served record**: every link of a record of a catch-up reply
is a record of the reply or one of its boundary digests. -/
theorem serve_closed (c : CheckedStore) (me : Me) (held : HeldMap) (q : Query)
    (hq : q.wanted = none) :
    ClosedRel hashSpec (replyRecords (serve c me held q)) (replyBoundary (serve c me held q)) := by
  obtain ⟨-, hF, hB⟩ := serve_abs c me held q hq
  rw [hF, hB]
  exact served_closed' hashSpec (c.closedRel _)

example : ClosedRel hashSpec
    (replyRecords (serve Examples.store Examples.meAlice Examples.held
      (Examples.rq Zrdt.Examples.bob Examples.keyBob)))
    (replyBoundary (serve Examples.store Examples.meAlice Examples.held
      (Examples.rq Zrdt.Examples.bob Examples.keyBob))) :=
  serve_closed _ _ _ _ rfl

/-- **Nothing extra**: every record of a catch-up reply is reachable from the reply's heads. -/
theorem serve_tight (c : CheckedStore) (me : Me) (held : HeldMap) (q : Query)
    (hq : q.wanted = none) :
    Tight hashSpec (replyRecords (serve c me held q))
      (headsRel hashSpec (replyRecords (serve c me held q))
        (replyBoundary (serve c me held q))) := by
  obtain ⟨-, hF, hB⟩ := serve_abs c me held q hq
  rw [hF, hB]
  exact served_tight' hashSpec (c.tightRel _)

example : Tight hashSpec
    (replyRecords (serve Examples.store Examples.meAlice Examples.held
      (Examples.rq Zrdt.Examples.bob Examples.keyBob)))
    (headsRel hashSpec
      (replyRecords (serve Examples.store Examples.meAlice Examples.held
        (Examples.rq Zrdt.Examples.bob Examples.keyBob)))
      (replyBoundary (serve Examples.store Examples.meAlice Examples.held
        (Examples.rq Zrdt.Examples.bob Examples.keyBob)))) :=
  serve_tight _ _ _ _ rfl

/-- **A boundary digest hides nothing `q` may see** (JOIN_PLAN §7.1, `serve_boundary`, in the
spec's words). A boundary digest of a catch-up reply is a digest the responder's view knows, and
from it, following links through the store, no record `q` may see is reachable. -/
theorem serve_boundary_spec {c : CheckedStore} {me : Me} {held : HeldMap} {q : Query}
    (hq : q.wanted = none) {d : Digest} (hb : Entry.boundary d ∈ serve c me held q) :
    d ∈ inView hashSpec (abs c) (boundarySpec me) ∧
      ∀ t ∈ abs c, visSpec c held q t → ¬ Reach hashSpec (abs c) {d} (hashSpec t) := by
  obtain ⟨-, -, hB⟩ := serve_abs c me held q hq
  exact served_boundary' hashSpec (hB ▸ mem_replyBoundary.mpr hb)

/-- **An `after` entry reaches a record `q` may see** (JOIN_PLAN §6.4, §7.1 `serve_after` with
`mem_reachersOf`). It is a record of the store, and a record of the store that `q` may see is
reachable from it. It carries structure, never content. This holds for per-digest requests
too. -/
theorem serve_after_reaches {c : CheckedStore} {me : Me} {held : HeldMap} {q : Query} {r : Rec}
    (he : Entry.after r ∈ serve c me held q) :
    toSpec r ∈ abs c ∧
      ∃ t ∈ abs c, visSpec c held q t ∧ Reach hashSpec (abs c) {hashRecord r} (hashSpec t) := by
  obtain ⟨d, hget, hup⟩ := serve_after he
  have h := (mem_servedF hashSpec).mp ((mem_upSet_of_get hget).mp hup)
  rw [hashSpec_toSpec] at h
  exact h

end Serve
end Zrdt
