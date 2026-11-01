/-
Copyright (c) 2026 zrdt contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: zrdt contributors
-/
import Mathlib
import Crdt.Merkle.ServeAbs
import Crdt.Merkle.ClassifyRel

set_option linter.unusedSectionVars false

/-!
# `SERVE` from a relative responder is the spec's served view (docs/JOIN_PLAN.md §7.2, §7.3)

`ServeAbs.lean` proves that `SERVE`'s catch-up reply from a closed store is the spec's served
view (`Rel.lean`). A member who joined late serves from a **relative** store (`RelStore`): some
links of its records point to boundary digests it holds no record for, and `zrdtd` passes the
store's `boundaryDigests` as the responder's own boundary (`Serve.Me.boundary`, `Zrdt.Proto`).
This file proves the same statements for that case: the running code (`Serve.serve` on
`c.raw`) serves exactly `servedF` and `servedB'` of the responder's records, with its own
boundary as `BS`.

* `Rel.serve_abs`: as `Serve.serve_abs`, for a relative store, for any `me`.
* `Rel.serve_heads`: the reply, as a view, has the heads of the responder's view;
  `Rel.serve_heads_code`: when `me.boundary` is the store's `boundaryDigests` (as `zrdtd` passes
  it), these are exactly the store's own heads (`HEADS`), so the newcomer shows the responder's
  compare code.
* `Rel.serve_closed`: when `me.boundary` holds the store's `boundaryDigests`, every link of a
  served record is a served record or a served boundary digest (Breaker 2's limit,
  `Rel.relative_responder_not_closed`, shows the hypothesis is needed).
* `Rel.serve_tight`: when the store has no cycle, every served record is reachable from the
  served heads.
* `Rel.serve_boundary_spec`, `Rel.serve_after_reaches`, `Rel.replyRecords_subset`: as in
  `ServeAbs.lean`.

The proofs follow `ServeAbs.lean`. The one change is the backward walk: it starts only from stored
digests (`mem_walk_linkedBy` takes `hL`), which `visList` always is.
-/

namespace Zrdt

open Crdt.Merkle

namespace RelStore

/-- `get` reads the spec store. -/
theorem get_eq_some_iff (c : RelStore) {d : Digest} {r : Rec} :
    c.get d = some r ↔ toSpec r ∈ c.raw.abs ∧ hashRecord r = d :=
  c.built.getElem?_eq_some_iff

/-- The walk's reachability is the spec's `Reach`, from the same digests. -/
theorem walkReach_iff (c : RelStore) (hs : Array Digest) {d : Digest} :
    WalkReach c.raw.map (fun r => r.links.toList) hs.toList d ↔
      Reach hashSpec c.raw.abs hs.toList.toFinset d := by
  constructor
  · intro h
    induction h with
    | start hd => exact .head (List.mem_toFinset.mpr hd)
    | @step k d v _ hkv hd ih =>
      refine .link (r := toSpec v) (RawStore.mem_abs.mpr ⟨k, v, hkv, rfl⟩) ?_
        (mem_toSpec_links.mpr (Array.mem_toList_iff.mp hd))
      rwa [hashSpec_toSpec, c.built.hash_eq k v hkv]
  · intro h
    induction h with
    | head hd => exact .start (List.mem_toFinset.mp hd)
    | @link x d hx _ hl ih =>
      obtain ⟨v, rfl, hv⟩ := c.built.exists_of_mem_abs hx
      rw [hashSpec_toSpec] at ih
      exact .step ih hv (Array.mem_toList_iff.mpr (mem_toSpec_links.mp hl))

/-- A relative store is closed relative to any boundary that holds its `boundaryDigests`. -/
theorem closedRel_of_boundary (c : RelStore) {me : Serve.Me}
    (hme : ∀ d ∈ c.boundaryDigests, d ∈ me.boundary) :
    ClosedRel hashSpec c.raw.abs (Serve.boundarySpec me) := by
  intro x hx d hd
  obtain ⟨k, r, hk, rfl⟩ := RawStore.mem_abs.mp hx
  rw [Crdt.Merkle.mem_inView, ← mem_digests, c.built.mem_digests_abs, Serve.mem_boundarySpec]
  by_cases hm : d ∈ c.raw.map
  · exact .inl hm
  · rcases c.built.closed k r hk d (mem_toSpec_links.mp hd) with h | h
    · exact .inl h
    · exact .inr (hme d (mem_boundaryDigests.mpr ⟨h, hm⟩))

/-- With `me.boundary` the store's `boundaryDigests`, the heads of the view with that boundary
are the store's heads. -/
theorem headsRel_boundaryDigests (c : RelStore) {me : Serve.Me}
    (hme : me.boundary = c.boundaryDigests) :
    headsRel hashSpec c.raw.abs (Serve.boundarySpec me) = c.heads.toList.toFinset := by
  rw [c.heads_toFinset]
  ext d
  rw [mem_headsRel, mem_headsRel]
  refine and_congr_left fun _ => ?_
  rw [c.built.mem_inView, Crdt.Merkle.mem_inView, ← mem_digests, c.built.mem_digests_abs,
    Serve.mem_boundarySpec, hme, mem_boundaryDigests]
  constructor
  · rintro (h | ⟨h, -⟩)
    · exact .inl h
    · exact .inr h
  · rintro (h | h)
    · exact .inl h
    · by_cases hm : d ∈ c.raw.map
      · exact .inl hm
      · exact .inr ⟨h, hm⟩

end RelStore

namespace Serve
namespace Rel

/-! ## Examples: Bob, a former newcomer, serves -/

namespace Examples

/-- Bob's relative store: `b1`, `c1` and `a2` accepted one by one over the boundary digest of
`a1`, which Alice vouched for (the records of `Zrdt.Examples.relStore`). -/
def bobRel : RelStore :=
  ((((RelStore.emptyWith Zrdt.Examples.group Zrdt.Examples.bnd (by decide)).accept
    Zrdt.Examples.b1).2.accept Zrdt.Examples.c1).2.accept Zrdt.Examples.a2).2

/-- Bob as a responder: his ACI, and his store's boundary digests (as `zrdtd` passes them). -/
def meBob : Me := { aci := Zrdt.Examples.bob, boundary := bobRel.boundaryDigests }

/-- `a1` is not stored in Bob's store (computed by the kernel). -/
theorem bobRel_not_a1 : bobRel.raw.map.contains (hashRecord Zrdt.Examples.a1) = false := by
  decide +kernel

/-- Bob's store has no cycle: its only boundary digest, `a1`'s, holds no record. -/
theorem bobRel_acyclic : Acyclic hashSpec bobRel.raw.abs := by
  refine bobRel.built.acyclic_of_unpromoted fun d hd hm => ?_
  have hd' : d = hashRecord Zrdt.Examples.a1 := by
    have : d ∈ Zrdt.Examples.bnd := hd
    simp only [Zrdt.Examples.bnd, Std.ExtTreeMap.mem_insert, Std.LawfulEqCmp.compare_eq_iff_eq,
      Std.ExtTreeMap.not_mem_empty, or_false] at this
    exact this.symm
  subst hd'
  rw [Std.ExtTreeMap.mem_iff_contains, bobRel_not_a1] at hm
  cases hm

end Examples

/-! ## What the requester may see -/

/-- The records the requester `q` may see (JOIN_PLAN §5's `vis`): the audience the responder
knows for the record seats `q` (`entitledHere`: from a matching held opening, else the audience
`zrdtd` recorded), and the record is not reachable from `q`'s `since` joined with the responder's
own `since` for that account. -/
def visSpec (c : RelStore) (held : HeldMap) (q : Query) (x : SpecRec) : Prop :=
  entitledHere held q (hashSpec x) (ofSpec x) = true ∧
    ¬ Reach hashSpec (c.raw.abs) (q.since ++ q.ownSince).toList.toFinset (hashSpec x)

/-- `visSpec` is decidable: `Reach` on a finite store is. -/
instance (c : RelStore) (held : HeldMap) (q : Query) : DecidablePred (visSpec c held q) :=
  fun _ => by unfold visSpec; infer_instance

-- A responder that holds no opening and no audience knows of no record that `q` may see.
example (c : RelStore) (q : Query) (x : SpecRec) : ¬ visSpec c ∅ q x := by
  simp [visSpec, entitledHere, audienceFor]

/-! ## The walks, in the spec's words -/

/-- `Serve.linkedByMap` is `linkedByRaw` of `core/Zrdt/Provenance.lean`: the same fold. -/
theorem linkedByMap_eq (c : RelStore) : linkedByMap c.raw = linkedByRaw c.raw := rfl

/-- **The backward walk, in the spec's words.** Walking `linkedByRaw` from stored digests `L`
finds exactly the stored records from which one of `L` is reachable. (A boundary digest is not a
start: it is not stored.) -/
theorem mem_walk_linkedBy (c : RelStore) (L : List Digest) (hL : ∀ v ∈ L, v ∈ c.raw.map)
    {x : Digest} :
    x ∈ walk id (linkedByRaw c.raw) ∅ L ↔
      x ∈ c.raw.map ∧ ∃ v ∈ L, Reach hashSpec (c.raw.abs) {x} v := by
  rw [mem_walk_iff, RawStore.mem_linkedByRaw, walkReach_iff_exists]
  refine and_congr_right fun hx => ⟨fun ⟨v, hv, hw⟩ => ⟨v, hv, ?_⟩, fun ⟨v, hv, hr⟩ => ⟨v, hv, ?_⟩⟩
  · have h := RawStore.mem_reachersOf c.raw c.built.hash_eq (hL v hv) (x := x)
    rw [reachersOf, mem_walk_iff, RawStore.mem_linkedByRaw] at h
    exact (h.mp ⟨hx, hw⟩).2
  · have h := RawStore.mem_reachersOf c.raw c.built.hash_eq (hL v hv) (x := x)
    rw [reachersOf, mem_walk_iff, RawStore.mem_linkedByRaw] at h
    exact (h.mpr ⟨hx, hr⟩).2

/-- `sinceReach` is the spec's reachability from `since` joined with the responder's own. -/
theorem mem_sinceReach {c : RelStore} {q : Query} {d : Digest} :
    d ∈ sinceReach c.raw q ↔
      d ∈ c.raw.map ∧ Reach hashSpec (c.raw.abs) (q.since ++ q.ownSince).toList.toFinset d := by
  rw [sinceReach, RawStore.reachSet, mem_walk_iff, RelStore.walkReach_iff]

/-- `visList` lists the stored records that `entitledHere` seats `q` in and that `since` does not
reach. -/
theorem mem_visList {c : RelStore} {held : HeldMap} {q : Query} {v : Digest} :
    v ∈ visList c.raw held q ↔
      ∃ r, c.get v = some r ∧ entitledHere held q v r = true ∧ v ∉ sinceReach c.raw q := by
  simp only [visList, List.mem_filterMap, Option.ite_none_right_eq_some, Bool.and_eq_true,
    Bool.not_eq_true', Prod.exists, Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some,
    Bool.eq_false_iff, ne_eq, Std.ExtTreeSet.contains_iff_mem, Option.some.injEq]
  constructor
  · rintro ⟨a, b, hget, ⟨he, hs⟩, rfl⟩
    exact ⟨b, hget, he, hs⟩
  · rintro ⟨r, hget, he, hs⟩
    exact ⟨v, r, hget, ⟨he, hs⟩, rfl⟩

/-- `upSet` holds the stored records from which a `visList` record is reachable. -/
theorem mem_upSet {c : RelStore} {held : HeldMap} {q : Query} {d : Digest} :
    d ∈ upSet c.raw held q ↔
      d ∈ c.raw.map ∧ ∃ v ∈ visList c.raw held q, Reach hashSpec (c.raw.abs) {d} v :=
  mem_walk_linkedBy c _ fun v hv => by
    obtain ⟨r, hr, -⟩ := mem_visList.mp hv
    exact Std.ExtTreeMap.mem_iff_isSome_getElem?.mpr (by
      rw [show c.raw.map[v]? = c.get v from rfl, hr]; rfl)

/-- `Serve.linksOf c.raw ds` holds the links of the stored records among `ds`. -/
theorem mem_linksOf_code {c : RelStore} {ds : List Digest} {d : Digest} :
    d ∈ Serve.linksOf c.raw ds ↔ ∃ k ∈ ds, ∃ r, c.get k = some r ∧ d ∈ r.links := by
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
def boundaryCond (c : RelStore) (held : HeldMap) (q : Query) (d : Digest) : Prop :=
  d ∈ Serve.linksOf c.raw (upSet c.raw held q).toList ∨
    d ∉ Serve.linksOf c.raw (c.raw.map.toList.map (·.1))

-- In the empty store nothing links anything, so every digest meets the condition.
example (g : GroupId) (held : HeldMap) (q : Query) (d : Digest) :
    boundaryCond (RelStore.empty g) held q d :=
  .inr fun h => by
    obtain ⟨k, hk, -⟩ := mem_linksOf_code.mp h
    simp [RelStore.empty, RelStore.emptyWith] at hk

/-- **The entries of a catch-up reply**, one case per line of JOIN_PLAN §5's table: each stored
record gives an `addressed` entry when `q` may see it, else an `after` entry when it is in the
walk, else a `boundary` entry when `boundaryCond` holds; each digest of the responder's own
boundary that the store does not hold gives a `boundary` entry when `boundaryCond` holds. -/
theorem mem_serve_catchup {c : RelStore} {me : Me} {held : HeldMap} {q : Query}
    (hq : q.wanted = none) {e : Entry} :
    e ∈ serve c.raw me held q ↔
      (∃ d r, c.get d = some r ∧
        ((entitledHere held q d r = true ∧ d ∉ sinceReach c.raw q ∧
            e = .addressed r ((held.getD d {}).opening.filter (serveOpening me q d r))
              (authorCopy me d r)) ∨
          (¬ (entitledHere held q d r = true ∧ d ∉ sinceReach c.raw q) ∧ d ∈ upSet c.raw held q ∧
            e = .after r) ∨
          (¬ (entitledHere held q d r = true ∧ d ∉ sinceReach c.raw q) ∧ d ∉ upSet c.raw held q ∧
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
theorem hash_of_get {c : RelStore} {d : Digest} {r : Rec} (h : c.get d = some r) :
    hashRecord r = d :=
  ((c.get_eq_some_iff).mp h).2

/-- A digest `get` finds is a key of the map. -/
theorem mem_map_of_get {c : RelStore} {d : Digest} {r : Rec} (h : c.get d = some r) :
    d ∈ c.raw.map :=
  Std.ExtTreeMap.mem_iff_isSome_getElem?.mpr (by rw [show c.raw.map[d]? = c.get d from rfl, h]; rfl)

/-- `visSpec` of a shipped record, in the code's words. -/
theorem visSpec_toSpec {c : RelStore} {held : HeldMap} {q : Query} {r : Rec} :
    visSpec c held q (toSpec r) ↔ entitledHere held q (hashRecord r) r = true ∧
      ¬ Reach hashSpec (c.raw.abs) (q.since ++ q.ownSince).toList.toFinset (hashRecord r) := by
  simp only [visSpec, hashSpec_toSpec, ofSpec_toSpec]

/-- `visSpec` of a stored record is the test `serve` makes: `entitledHere`, and `since` does not
reach it. -/
theorem visSpec_of_get {c : RelStore} {held : HeldMap} {q : Query} {d : Digest} {r : Rec}
    (h : c.get d = some r) :
    visSpec c held q (toSpec r) ↔ entitledHere held q d r = true ∧ d ∉ sinceReach c.raw q := by
  rw [visSpec_toSpec, hash_of_get h, mem_sinceReach]
  exact and_congr_right fun _ => ⟨fun hn hm => hn hm.2, fun hn hR => hn ⟨mem_map_of_get h, hR⟩⟩

/-- `visList` lists the digests of the records in `visSpec`. -/
theorem mem_visList_spec {c : RelStore} {held : HeldMap} {q : Query} {v : Digest} :
    v ∈ visList c.raw held q ↔ ∃ t ∈ c.raw.abs, visSpec c held q t ∧ hashSpec t = v := by
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
theorem mem_upSet_of_get {c : RelStore} {held : HeldMap} {q : Query} {d : Digest} {r : Rec}
    (h : c.get d = some r) :
    d ∈ upSet c.raw held q ↔ toSpec r ∈ servedF hashSpec (c.raw.abs) (visSpec c held q) := by
  rw [mem_upSet, mem_servedF, hashSpec_toSpec, hash_of_get h]
  simp only [mem_visList_spec]
  constructor
  · rintro ⟨-, v, ⟨t, ht, hv, rfl⟩, hR⟩
    exact ⟨((c.get_eq_some_iff).mp h).1, t, ht, hv, hR⟩
  · rintro ⟨-, t, ht, hv, hR⟩
    exact ⟨mem_map_of_get h, _, ⟨t, ht, hv, rfl⟩, hR⟩

/-- The records of `servedF` are the stored records in `upSet`. -/
theorem mem_servedF_iff {c : RelStore} {held : HeldMap} {q : Query} {x : SpecRec} :
    x ∈ servedF hashSpec (c.raw.abs) (visSpec c held q) ↔
      ∃ d r, c.get d = some r ∧ d ∈ upSet c.raw held q ∧ toSpec r = x := by
  constructor
  · intro hx
    obtain ⟨r, rfl, hr⟩ := c.built.exists_of_mem_abs (servedF_subset hashSpec _ _ hx)
    exact ⟨_, r, hr, (mem_upSet_of_get hr).mpr hx, rfl⟩
  · rintro ⟨d, r, hr, hu, rfl⟩
    exact (mem_upSet_of_get hr).mp hu

/-- `upSet` holds only stored digests. -/
theorem upSet_subset {c : RelStore} {held : HeldMap} {q : Query} {d : Digest}
    (h : d ∈ upSet c.raw held q) : d ∈ c.raw.map :=
  (mem_upSet.mp h).1

/-- The digests of `servedF` are `upSet`. -/
theorem mem_digests_servedF {c : RelStore} {held : HeldMap} {q : Query} {d : Digest} :
    d ∈ digests hashSpec (servedF hashSpec (c.raw.abs) (visSpec c held q)) ↔
      d ∈ upSet c.raw held q := by
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
theorem mem_linksOf_servedF {c : RelStore} {held : HeldMap} {q : Query} {d : Digest} :
    d ∈ Crdt.Merkle.linksOf (servedF hashSpec (c.raw.abs) (visSpec c held q)) ↔
      d ∈ Serve.linksOf c.raw (upSet c.raw held q).toList := by
  rw [mem_linksOf, mem_linksOf_code]
  constructor
  · rintro ⟨x, hx, hd⟩
    obtain ⟨k, r, hr, hu, rfl⟩ := mem_servedF_iff.mp hx
    exact ⟨k, Std.ExtTreeSet.mem_toList.mpr hu, r, hr, mem_toSpec_links.mp hd⟩
  · rintro ⟨k, hk, r, hr, hd⟩
    exact ⟨toSpec r, mem_servedF_iff.mpr ⟨k, r, hr, Std.ExtTreeSet.mem_toList.mp hk, rfl⟩,
      mem_toSpec_links.mpr hd⟩

/-- The links of the store are what `serve` computes as `linkedAny`. -/
theorem mem_linksOf_abs {c : RelStore} {d : Digest} :
    d ∈ Crdt.Merkle.linksOf (c.raw.abs) ↔ d ∈ Serve.linksOf c.raw (c.raw.map.toList.map (·.1)) := by
  rw [mem_linksOf, mem_linksOf_code]
  constructor
  · rintro ⟨x, hx, hd⟩
    obtain ⟨r, rfl, hr⟩ := c.built.exists_of_mem_abs hx
    exact ⟨_, List.mem_map.mpr ⟨(hashRecord r, r),
      Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some.mpr hr, rfl⟩, r, hr, mem_toSpec_links.mp hd⟩
  · rintro ⟨k, hk, r, hr, hd⟩
    exact ⟨toSpec r, ((c.get_eq_some_iff).mp hr).1, mem_toSpec_links.mpr hd⟩

/-- A record `q` may see is in the walk (the walk starts at it). -/
theorem mem_upSet_of_vis {c : RelStore} {held : HeldMap} {q : Query} {d : Digest} {r : Rec}
    (h : c.get d = some r) (hv : entitledHere held q d r = true ∧ d ∉ sinceReach c.raw q) :
    d ∈ upSet c.raw held q :=
  mem_upSet.mpr ⟨mem_map_of_get h, d, mem_visList.mpr ⟨r, h, hv⟩,
    .head (Finset.mem_singleton_self _)⟩

/-- In a catch-up, a record goes `addressed` exactly when `q` may see it. -/
theorem addressed_mem_serve {c : RelStore} {me : Me} {held : HeldMap} {q : Query}
    (hq : q.wanted = none) {r : Rec} :
    (∃ o ac, Entry.addressed r o ac ∈ serve c.raw me held q) ↔
      ∃ d, c.get d = some r ∧ entitledHere held q d r = true ∧ d ∉ sinceReach c.raw q := by
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
theorem after_mem_serve {c : RelStore} {me : Me} {held : HeldMap} {q : Query}
    (hq : q.wanted = none) {r : Rec} :
    Entry.after r ∈ serve c.raw me held q ↔
      ∃ d, c.get d = some r ∧ ¬ (entitledHere held q d r = true ∧ d ∉ sinceReach c.raw q) ∧
        d ∈ upSet c.raw held q := by
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
theorem boundary_mem_serve {c : RelStore} {me : Me} {held : HeldMap} {q : Query}
    (hq : q.wanted = none) {d : Digest} :
    Entry.boundary d ∈ serve c.raw me held q ↔
      (d ∈ c.raw.map ∨ d ∈ me.boundary) ∧ d ∉ upSet c.raw held q ∧ boundaryCond c held q d := by
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
theorem serve_abs (c : RelStore) (me : Me) (held : HeldMap) (q : Query)
    (hq : q.wanted = none) :
    replyAddressed (serve c.raw me held q) = (c.raw.abs).filter (visSpec c held q) ∧
      replyRecords (serve c.raw me held q) = servedF hashSpec (c.raw.abs) (visSpec c held q) ∧
      replyBoundary (serve c.raw me held q) =
        servedB' hashSpec (c.raw.abs) (visSpec c held q) (boundarySpec me) := by
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
      by_cases hv : entitledHere held q d r = true ∧ d ∉ sinceReach c.raw q
      · exact ⟨r, .inl ⟨d, hr, hv⟩, rfl⟩
      · exact ⟨r, .inr ⟨d, hr, hv, hu⟩, rfl⟩
  · ext d
    rw [mem_replyBoundary, boundary_mem_serve hq, mem_servedB', mem_inView, mem_digests_servedF,
      mem_linksOf_servedF, mem_linksOf_abs, mem_boundarySpec, boundaryCond]
    have hm : (∃ r ∈ c.raw.abs, hashSpec r = d) ↔ d ∈ c.raw.map := by
      rw [← mem_digests, c.built.mem_digests_abs]
    rw [hm]

-- On the store of the examples of `core/Zrdt/Serve.lean`: Bob's catch-up from Alice.
example : replyRecords (serve Examples.bobRel.raw Examples.meBob Examples.held
      (Examples.rq Zrdt.Examples.carol Examples.keyCarol)) =
    servedF hashSpec (Examples.bobRel.raw.abs)
      (visSpec Examples.bobRel Examples.held
        (Examples.rq Zrdt.Examples.carol Examples.keyCarol)) :=
  (serve_abs _ _ _ _ rfl).2.1

/-- The records of any reply are records of the store. -/
theorem replyRecords_subset (c : RelStore) (me : Me) (held : HeldMap) (q : Query) :
    replyRecords (serve c.raw me held q) ⊆ c.raw.abs := by
  intro x hx
  obtain ⟨r, ⟨o, ac, he⟩ | he, rfl⟩ := mem_replyRecords.mp hx
  · obtain ⟨d, hget, -⟩ := serve_addressed he
    exact ((c.get_eq_some_iff).mp hget).1
  · obtain ⟨d, hget, -⟩ := serve_after he
    exact ((c.get_eq_some_iff).mp hget).1

/-! ## What the newcomer's view is -/

/-- **A newcomer who caught up has the responder's heads** (JOIN_PLAN §6.7). The view of a
catch-up reply (its `addressed` and `after` records, and its boundary digests) has exactly the
heads of the responder's view: its store and its own boundary. No collision clause. -/
theorem serve_heads (c : RelStore) (me : Me) (held : HeldMap) (q : Query)
    (hq : q.wanted = none) :
    headsRel hashSpec (replyRecords (serve c.raw me held q))
        (replyBoundary (serve c.raw me held q)) =
      headsRel hashSpec (c.raw.abs) (boundarySpec me) := by
  obtain ⟨-, hF, hB⟩ := serve_abs c me held q hq
  rw [hF, hB]
  exact served_heads' hashSpec _ _ _

example : headsRel hashSpec
      (replyRecords (serve Examples.bobRel.raw Examples.meBob Examples.held
        (Examples.rq Zrdt.Examples.carol Examples.keyCarol)))
      (replyBoundary (serve Examples.bobRel.raw Examples.meBob Examples.held
        (Examples.rq Zrdt.Examples.carol Examples.keyCarol))) =
    headsRel hashSpec (Examples.bobRel.raw.abs) (boundarySpec Examples.meBob) :=
  serve_heads _ _ _ _ rfl

/-- **The newcomer can accept every served record**: every link of a record of a catch-up reply
is a record of the reply or one of its boundary digests. -/
theorem serve_closed (c : RelStore) (me : Me) (held : HeldMap) (q : Query)
    (hq : q.wanted = none) (hme : ∀ d ∈ c.boundaryDigests, d ∈ me.boundary) :
    ClosedRel hashSpec (replyRecords (serve c.raw me held q))
      (replyBoundary (serve c.raw me held q)) := by
  obtain ⟨-, hF, hB⟩ := serve_abs c me held q hq
  rw [hF, hB]
  exact served_closed' hashSpec (c.closedRel_of_boundary hme)

example : ClosedRel hashSpec
    (replyRecords (serve Examples.bobRel.raw Examples.meBob Examples.held
      (Examples.rq Zrdt.Examples.carol Examples.keyCarol)))
    (replyBoundary (serve Examples.bobRel.raw Examples.meBob Examples.held
      (Examples.rq Zrdt.Examples.carol Examples.keyCarol))) :=
  serve_closed _ _ _ _ rfl fun _ h => h

/-- **Nothing extra**: every record of a catch-up reply is reachable from the reply's heads. -/
theorem serve_tight (c : RelStore) (me : Me) (held : HeldMap) (q : Query)
    (hq : q.wanted = none) (hac : Acyclic hashSpec c.raw.abs) :
    Tight hashSpec (replyRecords (serve c.raw me held q))
      (headsRel hashSpec (replyRecords (serve c.raw me held q))
        (replyBoundary (serve c.raw me held q))) := by
  obtain ⟨-, hF, hB⟩ := serve_abs c me held q hq
  rw [hF, hB]
  exact served_tight' hashSpec (tight_of_acyclic hashSpec _ hac)

example : Tight hashSpec
    (replyRecords (serve Examples.bobRel.raw Examples.meBob Examples.held
      (Examples.rq Zrdt.Examples.carol Examples.keyCarol)))
    (headsRel hashSpec
      (replyRecords (serve Examples.bobRel.raw Examples.meBob Examples.held
        (Examples.rq Zrdt.Examples.carol Examples.keyCarol)))
      (replyBoundary (serve Examples.bobRel.raw Examples.meBob Examples.held
        (Examples.rq Zrdt.Examples.carol Examples.keyCarol)))) :=
  serve_tight _ _ _ _ rfl Examples.bobRel_acyclic

/-- **A boundary digest hides nothing `q` may see** (JOIN_PLAN §7.1, `serve_boundary`, in the
spec's words). A boundary digest of a catch-up reply is a digest the responder's view knows, and
from it, following links through the store, no record `q` may see is reachable. -/
theorem serve_boundary_spec {c : RelStore} {me : Me} {held : HeldMap} {q : Query}
    (hq : q.wanted = none) {d : Digest} (hb : Entry.boundary d ∈ serve c.raw me held q) :
    d ∈ inView hashSpec (c.raw.abs) (boundarySpec me) ∧
      ∀ t ∈ c.raw.abs, visSpec c held q t → ¬ Reach hashSpec (c.raw.abs) {d} (hashSpec t) := by
  obtain ⟨-, -, hB⟩ := serve_abs c me held q hq
  exact served_boundary' hashSpec (hB ▸ mem_replyBoundary.mpr hb)

/-- **An `after` entry reaches a record `q` may see** (JOIN_PLAN §6.4, §7.1 `serve_after` with
`mem_reachersOf`). It is a record of the store, and a record of the store that `q` may see is
reachable from it. It carries structure, never content. This holds for per-digest requests
too. -/
theorem serve_after_reaches {c : RelStore} {me : Me} {held : HeldMap} {q : Query} {r : Rec}
    (he : Entry.after r ∈ serve c.raw me held q) :
    toSpec r ∈ c.raw.abs ∧
      ∃ t ∈ c.raw.abs, visSpec c held q t ∧
        Reach hashSpec (c.raw.abs) {hashRecord r} (hashSpec t) := by
  obtain ⟨d, hget, hup⟩ := serve_after he
  have h := (mem_servedF hashSpec).mp ((mem_upSet_of_get hget).mp hup)
  rw [hashSpec_toSpec] at h
  exact h


/-- **A newcomer served by a former newcomer shows the responder's compare code.** When
`me.boundary` is the responder's `boundaryDigests` (as `zrdtd` passes it), the catch-up reply,
as a view, has exactly the responder's heads (`HEADS`). No collision clause. -/
theorem serve_heads_code (c : RelStore) (me : Me) (held : HeldMap) (q : Query)
    (hq : q.wanted = none) (hme : me.boundary = c.boundaryDigests) :
    headsRel hashSpec (replyRecords (serve c.raw me held q))
        (replyBoundary (serve c.raw me held q)) = c.heads.toList.toFinset := by
  rw [serve_heads c me held q hq, c.headsRel_boundaryDigests hme]

example : headsRel hashSpec
      (replyRecords (serve Examples.bobRel.raw Examples.meBob Examples.held
        (Examples.rq Zrdt.Examples.carol Examples.keyCarol)))
      (replyBoundary (serve Examples.bobRel.raw Examples.meBob Examples.held
        (Examples.rq Zrdt.Examples.carol Examples.keyCarol))) =
    Examples.bobRel.heads.toList.toFinset :=
  serve_heads_code _ _ _ _ rfl rfl

end Rel
end Serve
end Zrdt
