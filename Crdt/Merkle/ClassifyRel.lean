/-
Copyright (c) 2026 zrdt contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: zrdt contributors
-/
import Mathlib
import Crdt.Merkle.ClassifyStatus
import Crdt.Merkle.RelRefine

set_option linter.unusedSectionVars false

/-!
# `CLASSIFY` on a store with a boundary (docs/JOIN_PLAN.md §7.3, `classify_spec`)

`zrdtd` runs `classifyRaw` on a relative store (`ChatStore.classify`, `core/Zrdt/Provenance.lean`):
the same code as `classify`, over the records of any raw store. `ClassifyFast.lean` and
`ClassifyStatus.lean` prove that `classify` computes the spec's `status` on a closed store. This
file proves the same for `classifyRaw` on any raw store that has the two properties those proofs
use (`ReadyStore`):

* every record is stored under its own digest (`BuiltRel.hash_eq`, true of every relative store);
* the records have no cycle (`Acyclic`). A closed store has none (`acyclic_of_acceptBuilt`); a
  relative store has none when no record was promoted (`BuiltRel.acyclic_of_unpromoted`), and a
  cycle through a promoted record needs a record whose digest was written into a record its own
  digest depends on (`RelSpec.lean`).

A link to a digest that is not stored (a boundary digest) is followed nowhere, by the code and by
the spec (`Reach` only steps through records of the store), so the boundary changes nothing else.

* `ReadyStore.classify_spec`: `classifyRaw` gives each stored record the spec's `status`, and
  nothing else a status.
* `RelStore.classify_model`: so for a relative store without a cycle.
* `ReadyStore.ofChecked`: a closed store is ready; there `classifyRaw` is `classify`
  (`classify_raw`), and `ReadyStore.classify_spec` says what `CheckedStore.classify_spec` says.

The proofs follow `ClassifyFast.lean` step by step. The one change is `mem_reachersOf`: the walk
backwards from a digest finds the records that reach it when the digest is stored (in a closed
store every link is stored; here a link may be a boundary digest).
-/

namespace Zrdt

open Crdt.Merkle

/-- A raw store with what `CLASSIFY`'s proofs need: each record is stored under its own digest,
and the records have no cycle. -/
structure ReadyStore where
  /-- The records and heads. -/
  raw : RawStore
  /-- Every record is stored under its own digest. -/
  hash_eq : ∀ (k : Digest) (r : Rec), raw.map[k]? = some r → hashRecord r = k
  /-- Following one or more links from a record never leads back to it. -/
  acyclic : Acyclic hashSpec raw.abs

namespace ReadyStore

/-- A closed store is ready: its records have no cycle (`acyclic_of_acceptBuilt`). -/
def ofChecked (c : CheckedStore) : ReadyStore :=
  ⟨c.raw, c.built.hash_eq, acyclic_of_acceptBuilt hashSpec c.acceptBuilt c.built.no_collision⟩

/-- A relative store with no cycle is ready. -/
def ofRel (c : RelStore) (hac : Acyclic hashSpec c.raw.abs) : ReadyStore :=
  ⟨c.raw, c.built.hash_eq, hac⟩

example : (ofChecked (CheckedStore.empty Examples.group)).raw.map = ∅ := rfl

/-- The record with digest `d`, if stored. -/
def get (c : ReadyStore) (d : Digest) : Option Rec := c.raw.map[d]?

/-- The stored records reached from `start` (`RawStore.reachSet`). -/
def reachSet (c : ReadyStore) (start : Array Digest) : DigestSet := c.raw.reachSet start

/-- Every spec record of the store is the spec record of a record stored under its digest. -/
theorem exists_of_mem_abs (c : ReadyStore) {x : SpecRec} (hx : x ∈ c.raw.abs) :
    ∃ r, toSpec r = x ∧ c.raw.map[hashRecord r]? = some r := by
  obtain ⟨k, r, hk, rfl⟩ := RawStore.mem_abs.mp hx
  exact ⟨r, rfl, by rwa [c.hash_eq k r hk]⟩

/-- `get` reads the spec store. -/
theorem get_eq_some_iff (c : ReadyStore) {d : Digest} {r : Rec} :
    c.get d = some r ↔ toSpec r ∈ c.raw.abs ∧ hashRecord r = d := by
  constructor
  · intro hk
    exact ⟨RawStore.mem_abs.mpr ⟨d, r, hk, rfl⟩, c.hash_eq d r hk⟩
  · rintro ⟨hr, rfl⟩
    obtain ⟨k, r', hk, he⟩ := RawStore.mem_abs.mp hr
    obtain rfl := toSpec_injective he
    show c.raw.map[hashRecord _]? = _
    rw [c.hash_eq k _ hk]
    exact hk

/-- A digest is stored exactly when the spec store holds a record with that digest. -/
theorem mem_digests_abs (c : ReadyStore) {d : Digest} :
    d ∈ digests hashSpec c.raw.abs ↔ d ∈ c.raw.map := by
  rw [mem_digests, Std.ExtTreeMap.mem_iff_isSome_getElem?, Option.isSome_iff_exists]
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨k, r, hk, rfl⟩ := RawStore.mem_abs.mp hx
    rw [hashSpec_toSpec, c.hash_eq k r hk]
    exact ⟨r, hk⟩
  · rintro ⟨r, hr⟩
    exact ⟨toSpec r, RawStore.mem_abs.mpr ⟨d, r, hr, rfl⟩,
      by rw [hashSpec_toSpec, c.hash_eq d r hr]⟩

/-- The walk's reachability is the spec's `Reach`, from the same digests. -/
theorem walkReach_iff (c : ReadyStore) (hs : Array Digest) {d : Digest} :
    WalkReach c.raw.map (fun r => r.links.toList) hs.toList d ↔
      Reach hashSpec c.raw.abs hs.toList.toFinset d := by
  constructor
  · intro h
    induction h with
    | start hd => exact .head (List.mem_toFinset.mpr hd)
    | @step k d v _ hkv hd ih =>
      refine .link (r := toSpec v) (RawStore.mem_abs.mpr ⟨k, v, hkv, rfl⟩) ?_
        (mem_toSpec_links.mpr (Array.mem_toList_iff.mp hd))
      rwa [hashSpec_toSpec, c.hash_eq k v hkv]
  · intro h
    induction h with
    | head hd => exact .start (List.mem_toFinset.mp hd)
    | @link x d hx _ hl ih =>
      obtain ⟨v, rfl, hv⟩ := c.exists_of_mem_abs hx
      rw [hashSpec_toSpec] at ih
      exact .step ih hv (Array.mem_toList_iff.mpr (mem_toSpec_links.mp hl))

/-- `reachSet` is the spec's `reachSet`. -/
theorem reachSet_iff (c : ReadyStore) (hs : Array Digest) {d : Digest} :
    d ∈ c.reachSet hs ↔
      d ∈ digests hashSpec (Crdt.Merkle.reachSet hashSpec c.raw.abs hs.toList.toFinset) := by
  rw [reachSet, RawStore.reachSet, mem_walk_iff, walkReach_iff, mem_digests]
  constructor
  · rintro ⟨hdm, hR⟩
    obtain ⟨x, hx, rfl⟩ := (mem_digests hashSpec).mp (c.mem_digests_abs.mpr hdm)
    exact ⟨x, (mem_reachSet hashSpec).mpr ⟨hx, hR⟩, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨hx, hR⟩ := (mem_reachSet hashSpec).mp hx
    exact ⟨c.mem_digests_abs.mp ((mem_digests hashSpec).mpr ⟨x, hx, rfl⟩), hR⟩

/-- The live records of author `a` in the spec, read as stored live records. -/
theorem exists_liveRecords {c : ReadyStore} {facts : Array Fact} {a : Aci}
    {Q : SpecRec → Prop} :
    (∃ y ∈ liveRecords hashSpec c.raw.abs (liveOf facts) a, Q y) ↔
      ∃ l x dis, (liveFacts facts)[l]? = some dis ∧ c.get l = some x ∧ x.author = a ∧
        Q (toSpec x) := by
  simp only [liveRecords, Finset.mem_filter]
  constructor
  · rintro ⟨y, ⟨hy, hl, ha⟩, hq⟩
    obtain ⟨x, rfl, hx⟩ := c.exists_of_mem_abs hy
    rw [hashSpec_toSpec, ← mem_liveFacts, Std.ExtTreeMap.mem_iff_isSome_getElem?,
      Option.isSome_iff_exists] at hl
    obtain ⟨dis, hdis⟩ := hl
    exact ⟨_, x, dis, hdis, hx, ha, hq⟩
  · rintro ⟨l, x, dis, hdis, hx, ha, hq⟩
    obtain ⟨hxs, rfl⟩ := (c.get_eq_some_iff).mp hx
    refine ⟨toSpec x, ⟨hxs, ?_, ha⟩, hq⟩
    rw [hashSpec_toSpec, ← mem_liveFacts, Std.ExtTreeMap.mem_iff_isSome_getElem?, hdis]
    rfl

end ReadyStore

/-! ## Links followed backwards, in any raw store -/

namespace RawStore


/-- `linkedBy` is the fold of `linkStep` over the stored records. -/
theorem linkedByRaw_eq (c : RawStore) :
    linkedByRaw c = c.map.toList.foldl linkStep (c.map.map fun _ _ => []) := by
  rw [Zrdt.linkedByRaw, Std.ExtTreeMap.foldl_eq_foldl_toList]
  rfl

private theorem foldl_modify (d : Digest) (ls : List Digest)
    (m : Std.ExtTreeMap Digest (List Digest) compare) (k : Digest) :
    (k ∈ ls.foldl (fun m l => m.modify l (d :: ·)) m ↔ k ∈ m) ∧
    ∀ v', (ls.foldl (fun m l => m.modify l (d :: ·)) m)[k]? = some v' →
      ∃ v, m[k]? = some v ∧ ∀ x, x ∈ v' ↔ x ∈ v ∨ (x = d ∧ k ∈ ls) := by
  induction ls generalizing m with
  | nil =>
    refine ⟨Iff.rfl, fun v' h => ⟨v', h, fun x => by simp⟩⟩
  | cons l ls ih =>
    obtain ⟨ih1, ih2⟩ := ih (m.modify l (d :: ·))
    simp only [List.foldl_cons]
    refine ⟨by rw [ih1, Std.ExtTreeMap.mem_modify], fun v' hv' => ?_⟩
    obtain ⟨v1, hv1, hx⟩ := ih2 v' hv'
    rw [Std.ExtTreeMap.getElem?_modify] at hv1
    split at hv1
    · rename_i hlk
      rw [Digest.compare_eq_iff] at hlk
      subst hlk
      obtain ⟨v, hv, rfl⟩ := Option.map_eq_some_iff.mp hv1
      refine ⟨v, hv, fun x => ?_⟩
      rw [hx x]
      simp only [List.mem_cons, true_or, and_true]
      tauto
    · rename_i hlk
      rw [Digest.compare_eq_iff] at hlk
      refine ⟨v1, hv1, fun x => ?_⟩
      rw [hx x, List.mem_cons]
      constructor
      · rintro (h | ⟨rfl, h⟩)
        · exact Or.inl h
        · exact Or.inr ⟨rfl, Or.inr h⟩
      · rintro (h | ⟨rfl, rfl | h⟩)
        · exact Or.inl h
        · exact absurd rfl hlk
        · exact Or.inr ⟨rfl, h⟩

private theorem foldl_linkStep (ps : List (Digest × Rec))
    (m : Std.ExtTreeMap Digest (List Digest) compare) (k : Digest) :
    (k ∈ ps.foldl linkStep m ↔ k ∈ m) ∧
    ∀ v', (ps.foldl linkStep m)[k]? = some v' →
      ∃ v, m[k]? = some v ∧ ∀ x, x ∈ v' ↔ x ∈ v ∨ ∃ y, (x, y) ∈ ps ∧ k ∈ y.links := by
  induction ps generalizing m with
  | nil => exact ⟨Iff.rfl, fun v' h => ⟨v', h, fun x => by simp⟩⟩
  | cons p ps ih =>
    obtain ⟨ih1, ih2⟩ := ih (linkStep m p)
    have hstep := foldl_modify p.1 p.2.links.toList m k
    rw [Array.foldl_toList] at hstep
    simp only [List.foldl_cons]
    refine ⟨by rw [ih1]; exact hstep.1, fun v' hv' => ?_⟩
    obtain ⟨v1, hv1, hx⟩ := ih2 v' hv'
    obtain ⟨v, hv, hx1⟩ := hstep.2 v1 hv1
    refine ⟨v, hv, fun x => ?_⟩
    rw [hx x, hx1 x]
    simp only [Array.mem_toList_iff]
    constructor
    · rintro ((h | ⟨rfl, h⟩) | ⟨y, hy, h⟩)
      · exact Or.inl h
      · exact Or.inr ⟨p.2, List.mem_cons_self, h⟩
      · exact Or.inr ⟨y, List.mem_cons_of_mem _ hy, h⟩
    · rintro (h | ⟨y, hy, h⟩)
      · exact Or.inl (Or.inl h)
      · rcases List.mem_cons.mp hy with he | hy
        · subst he; exact Or.inl (Or.inr ⟨rfl, h⟩)
        · exact Or.inr ⟨y, hy, h⟩

/-- The keys of `linkedBy` are the stored digests. -/
theorem mem_linkedByRaw (c : RawStore) {k : Digest} : k ∈ linkedByRaw c ↔ k ∈ c.map := by
  rw [linkedByRaw_eq, (foldl_linkStep _ _ k).1, Std.ExtTreeMap.mem_map]

/-- **`linkedBy` lists exactly the stored records that link a digest.** -/
theorem linkedByRaw_get (c : RawStore) {k : Digest} {v : List Digest}
    (h : (linkedByRaw c)[k]? = some v) {x : Digest} :
    x ∈ v ↔ ∃ y, c.map[x]? = some y ∧ k ∈ y.links := by
  rw [linkedByRaw_eq] at h
  obtain ⟨v0, hv0, hx⟩ := (foldl_linkStep _ _ k).2 v h
  rw [Std.ExtTreeMap.getElem?_map] at hv0
  obtain ⟨_, -, rfl⟩ := Option.map_eq_some_iff.mp hv0
  rw [hx x]
  simp only [List.not_mem_nil, false_or, Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some]

/-- **`reachersOf` finds exactly the stored records that reach `d`.** -/
theorem mem_reachersOf (c : RawStore)
    (hh : ∀ (k : Digest) (r : Rec), c.map[k]? = some r → hashRecord r = k) {d x : Digest}
    (hd : d ∈ c.map) :
    x ∈ reachersOf (linkedByRaw c) d ↔ x ∈ c.map ∧ Reach hashSpec (c.abs) {x} d := by
  rw [reachersOf, mem_walk_iff, mem_linkedByRaw]
  refine and_congr_right fun hx => ⟨fun h => ?_, fun h => ?_⟩
  · clear hx hd
    induction h with
    | start hd => rw [List.mem_singleton] at hd; subst hd; exact .head (Finset.mem_singleton_self _)
    | @step k x v _ hk hxv ih =>
      obtain ⟨y, hy, hky⟩ := (linkedByRaw_get c hk).mp hxv
      have hxy : hashRecord y = x := hh x y hy
      refine Reach.trans hashSpec ?_ ih
      refine .link (r := toSpec y) (RawStore.mem_abs.mpr ⟨x, y, hy, rfl⟩) ?_
        (mem_toSpec_links.mpr hky)
      rw [hashSpec_toSpec, hxy]
      exact .head (Finset.mem_singleton_self _)
  · -- A path to a stored digest passes only through stored records.
    suffices key : ∀ d', Reach hashSpec c.abs {x} d' → d' ∈ c.map →
        WalkReach (linkedByRaw c) id [d'] x from key d h hd
    intro d' h'
    induction h' with
    | head hd0 =>
      intro _
      rw [Finset.mem_singleton] at hd0
      subst hd0
      exact .start List.mem_cons_self
    | @link y d' hy _ hl ih =>
      intro hd'
      obtain ⟨k, r, hk, rfl⟩ := RawStore.mem_abs.mp hy
      have hr : c.map[hashRecord r]? = some r := by rwa [hh k r hk]
      rw [hashSpec_toSpec] at ih
      have hl' : d' ∈ r.links := mem_toSpec_links.mp hl
      obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp
        (Std.ExtTreeMap.mem_iff_isSome_getElem?.mp ((mem_linkedByRaw c).mpr hd'))
      have hrv : hashRecord r ∈ v := (linkedByRaw_get c hv).mpr ⟨r, hr, hl'⟩
      have hrm : hashRecord r ∈ c.map :=
        Std.ExtTreeMap.mem_iff_isSome_getElem?.mpr (by simp [hr])
      exact WalkReach.trans (.step (.start List.mem_cons_self) hv hrv) (ih hrm)

/-- **`reachersOf` on a ready store**: the stored records that reach a stored digest. -/
theorem _root_.Zrdt.ReadyStore.mem_reachersOf (c : ReadyStore) {d x : Digest} (hd : d ∈ c.raw.map) :
    x ∈ reachersOf (linkedByRaw c.raw) d ↔ x ∈ c.raw.map ∧ Reach hashSpec c.raw.abs {x} d :=
  Zrdt.RawStore.mem_reachersOf c.raw c.hash_eq hd

end RawStore

namespace ReadyStore

/-! ## Records that reach every one of a list -/

/-! ## The author views -/

/-- One step of the `byAuthor` fold in `authorViews`. -/
def authorStep (c : ReadyStore) (m : Std.ExtTreeMap Aci (Array Digest × DigestSet) compare)
    (p : Digest × Array Digest) : Std.ExtTreeMap Aci (Array Digest × DigestSet) compare :=
  match c.get p.1 with
  | some r =>
    let (ls, ds) := m.getD r.author (#[], ∅)
    m.insert r.author (ls.push p.1, p.2.foldl (fun s x => s.insert x) ds)
  | none => m

-- A live digest that is not stored adds nothing.
example : authorStep (ReadyStore.ofChecked (CheckedStore.empty Examples.group)) ∅
    (Examples.dig 9, #[]) = ∅ := rfl

/-- The view of one author, from its live digests `ls` and disowned digests `ds`. -/
def viewOf (c : ReadyStore) (p : Array Digest × DigestSet) : AuthorView :=
  let below := c.reachSet (p.1.flatMap fun l => ((c.get l).map (·.links)).getD #[])
  let newest := p.1.filter (!below.contains ·)
  ⟨c.reachSet p.1, p.2, reachersOfAll (linkedByRaw c.raw) newest⟩

/-- `authorViews` is `viewOf` on the fold of `authorStep`. -/
theorem authorViews_eq (c : ReadyStore) (live : Std.ExtTreeMap Digest (Array Digest) compare) :
    authorViewsRaw c.raw live = (live.toList.foldl (authorStep c) ∅).map fun _ p => viewOf c p := by
  rw [authorViewsRaw, Std.ExtTreeMap.foldl_eq_foldl_toList]
  rfl

/-- One `authorStep`, for author `a`. -/
theorem entryIs_step (c : ReadyStore) {m : Std.ExtTreeMap Aci (Array Digest × DigestSet) compare}
    {a : Aci} {L E : Digest → Prop} (h : EntryIs m[a]? L E) (p : Digest × Array Digest) :
    EntryIs (authorStep c m p)[a]?
      (fun l => L l ∨ (l = p.1 ∧ ∃ y, c.get p.1 = some y ∧ y.author = a))
      (fun e => E e ∨ ((∃ y, c.get p.1 = some y ∧ y.author = a) ∧ e ∈ p.2)) := by
  unfold authorStep
  cases hg : c.get p.1 with
  | none => exact h.congr (fun l => by simp) (fun e => by simp)
  | some y =>
    dsimp only
    by_cases hya : y.author = a
    · subst hya
      rw [Std.ExtTreeMap.getD_eq_getD_getElem?]
      cases hm : m[y.author]? with
      | none =>
        rw [hm] at h
        simp only [Option.getD_none, Std.ExtTreeMap.getElem?_insert_self]
        refine ⟨fun l => ?_, fun e => ?_, p.1, Or.inr ⟨rfl, y, rfl, rfl⟩⟩
        · simp only [Array.push_empty, Array.mem_singleton]
          have := h.1 l
          constructor
          · rintro rfl; exact Or.inr ⟨rfl, y, rfl, rfl⟩
          · rintro (h' | ⟨rfl, -⟩)
            · exact absurd h' this
            · rfl
        · rw [← Array.foldl_toList, mem_foldl_insert, Array.mem_toList_iff]
          have := h.2 e
          simp only [Std.ExtTreeSet.not_mem_empty, false_or]
          constructor
          · intro he; exact Or.inr ⟨⟨y, rfl, rfl⟩, he⟩
          · rintro (h' | ⟨-, he⟩)
            · exact absurd h' this
            · exact he
      | some q =>
        rw [hm] at h
        obtain ⟨h1, h2, l0, hl0⟩ := h
        simp only [Option.getD_some, Std.ExtTreeMap.getElem?_insert_self]
        refine ⟨fun l => ?_, fun e => ?_, l0, Or.inl hl0⟩
        · simp only [Array.mem_push, h1]
          constructor
          · rintro (h' | rfl)
            · exact Or.inl h'
            · exact Or.inr ⟨rfl, y, rfl, rfl⟩
          · rintro (h' | ⟨rfl, -⟩)
            · exact Or.inl h'
            · exact Or.inr rfl
        · rw [← Array.foldl_toList, mem_foldl_insert, Array.mem_toList_iff, h2]
          constructor
          · rintro (h' | h')
            · exact Or.inl h'
            · exact Or.inr ⟨⟨y, rfl, rfl⟩, h'⟩
          · rintro (h' | ⟨-, h'⟩)
            · exact Or.inl h'
            · exact Or.inr h'
    · have hne : compare y.author a ≠ .eq := fun h => hya (Std.LawfulEqCmp.compare_eq_iff_eq.mp h)
      simp only [Std.ExtTreeMap.getElem?_insert, hne, ↓reduceIte]
      refine h.congr (fun l => ?_) (fun e => ?_)
      · constructor
        · exact Or.inl
        · rintro (h' | ⟨-, y', hy', ha⟩)
          · exact h'
          · cases hy'; exact absurd ha hya
      · constructor
        · exact Or.inl
        · rintro (h' | ⟨⟨y', hy', ha⟩, -⟩)
          · exact h'
          · cases hy'; exact absurd ha hya

/-- The whole `byAuthor` fold, for author `a`. -/
theorem entryIs_foldl (c : ReadyStore) (ps : List (Digest × Array Digest))
    {m : Std.ExtTreeMap Aci (Array Digest × DigestSet) compare} {a : Aci} {L E : Digest → Prop}
    (h : EntryIs m[a]? L E) :
    EntryIs (ps.foldl (authorStep c) m)[a]?
      (fun l => L l ∨ ∃ dis, (l, dis) ∈ ps ∧ ∃ y, c.get l = some y ∧ y.author = a)
      (fun e => E e ∨ ∃ l dis, (l, dis) ∈ ps ∧ (∃ y, c.get l = some y ∧ y.author = a) ∧
        e ∈ dis) := by
  induction ps generalizing m L E with
  | nil => exact h.congr (fun l => by simp) (fun e => by simp)
  | cons p ps ih =>
    rw [List.foldl_cons]
    refine (ih (entryIs_step c h p)).congr (fun l => ?_) (fun e => ?_)
    · constructor
      · rintro ((h' | ⟨rfl, hq⟩) | ⟨dis, hd, hq⟩)
        · exact Or.inl h'
        · exact Or.inr ⟨p.2, List.mem_cons_self, hq⟩
        · exact Or.inr ⟨dis, List.mem_cons_of_mem _ hd, hq⟩
      · rintro (h' | ⟨dis, hd, hq⟩)
        · exact Or.inl (Or.inl h')
        · rcases List.mem_cons.mp hd with he | hd
          · subst he; exact Or.inl (Or.inr ⟨rfl, hq⟩)
          · exact Or.inr ⟨dis, hd, hq⟩
    · constructor
      · rintro ((h' | ⟨hq, he⟩) | ⟨l, dis, hd, hq, he⟩)
        · exact Or.inl h'
        · exact Or.inr ⟨p.1, p.2, List.mem_cons_self, hq, he⟩
        · exact Or.inr ⟨l, dis, List.mem_cons_of_mem _ hd, hq, he⟩
      · rintro (h' | ⟨l, dis, hd, hq, he⟩)
        · exact Or.inl (Or.inl h')
        · rcases List.mem_cons.mp hd with hp | hd
          · subst hp; exact Or.inl (Or.inr ⟨hq, he⟩)
          · exact Or.inr ⟨l, dis, hd, hq, he⟩

/-- **The `byAuthor` entry of author `a`**: none when `a` has no stored live record; otherwise
exactly `a`'s stored live digests (at least one), and the union of their disown lists. -/
theorem byAuthor_entry (c : ReadyStore) (live : Std.ExtTreeMap Digest (Array Digest) compare)
    (a : Aci) :
    EntryIs (live.toList.foldl (authorStep c) ∅)[a]?
      (fun l => ∃ dis y, live[l]? = some dis ∧ c.get l = some y ∧ y.author = a)
      (fun e => ∃ l dis y, live[l]? = some dis ∧ c.get l = some y ∧ y.author = a ∧ e ∈ dis) := by
  have h0 : EntryIs (∅ : Std.ExtTreeMap Aci (Array Digest × DigestSet) compare)[a]?
      (fun _ => False) (fun _ => False) := by
    rw [Std.ExtTreeMap.getElem?_empty]; exact ⟨fun _ h => h, fun _ h => h⟩
  refine (entryIs_foldl c live.toList h0).congr (fun l => ?_) (fun e => ?_)
  · simp only [false_or, Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some]
    constructor
    · rintro ⟨dis, hd, y, hy, ha⟩; exact ⟨dis, y, hd, hy, ha⟩
    · rintro ⟨dis, y, hd, hy, ha⟩; exact ⟨dis, hd, y, hy, ha⟩
  · simp only [false_or, Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some]
    constructor
    · rintro ⟨l, dis, hd, ⟨y, hy, ha⟩, he⟩; exact ⟨l, dis, y, hd, hy, ha, he⟩
    · rintro ⟨l, dis, y, hd, hy, ha, he⟩; exact ⟨l, dis, hd, ⟨y, hy, ha⟩, he⟩

/-! ## The newest live records -/

/-- What `reachSet` returns, as spec reachability from one of the start digests. -/
theorem mem_reachSet_code (c : ReadyStore) (S : Array Digest) {x : Digest} :
    x ∈ c.reachSet S ↔ x ∈ c.raw.map ∧ ∃ k ∈ S, Reach hashSpec (c.raw.abs) {k} x := by
  rw [ReadyStore.reachSet_iff, mem_digests]
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨hy, hR⟩ := (mem_reachSet hashSpec).mp hy
    obtain ⟨k, hk, hR⟩ := (reach_iff_exists hashSpec).mp hR
    exact ⟨c.mem_digests_abs.mp ((mem_digests hashSpec).mpr ⟨y, hy, rfl⟩), k,
      Array.mem_toList_iff.mp (List.mem_toFinset.mp hk), hR⟩
  · rintro ⟨hx, k, hk, hR⟩
    obtain ⟨y, hy, rfl⟩ := (mem_digests hashSpec).mp (c.mem_digests_abs.mpr hx)
    refine ⟨y, (mem_reachSet hashSpec).mpr ⟨hy, ?_⟩, rfl⟩
    exact (reach_iff_exists hashSpec).mpr
      ⟨k, List.mem_toFinset.mpr (Array.mem_toList_iff.mpr hk), hR⟩

/-- The live records of a list that no other of them reaches through a link (the `newest` of
`authorViews`). -/
def newestOf (c : ReadyStore) (ls : Array Digest) : Array Digest :=
  ls.filter (!(c.reachSet (ls.flatMap fun l => ((c.get l).map (·.links)).getD #[])).contains ·)

example (c : ReadyStore) : newestOf c #[] = #[] := rfl
example (c : ReadyStore) : (viewOf c (#[], ∅)).disowned = ∅ := rfl

/-- `viewOf`'s third field is `reachersOfAll` of the newest records. -/
theorem viewOf_reachesAllLive (c : ReadyStore) (p : Array Digest × DigestSet) :
    (viewOf c p).reachesAllLive = reachersOfAll (linkedByRaw c.raw) (newestOf c p.1) := rfl

/-- A stored record reaches `l` if it reaches a link of the record stored under `l`. -/
theorem reach_of_link (c : ReadyStore) {l k x : Digest} {y : Rec} (hy : c.get l = some y)
    (hk : k ∈ y.links) (hR : Reach hashSpec (c.raw.abs) {k} x) :
    Reach hashSpec (c.raw.abs) {l} x := by
  obtain ⟨hy', rfl⟩ := (c.get_eq_some_iff).mp hy
  refine Reach.trans hashSpec ?_ hR
  refine .link hy' ?_ (mem_toSpec_links.mpr hk)
  rw [hashSpec_toSpec]
  exact .head (Finset.mem_singleton_self _)

/-- **Every record of the list is reached from a newest one**, since a store has no cycles. -/
theorem exists_newest (c : ReadyStore) (ls : Array Digest) :
    ∀ l ∈ ls, ∃ n ∈ newestOf c ls, Reach hashSpec (c.raw.abs) {n} l := by
  classical
  have hac : Acyclic hashSpec (c.raw.abs) :=
    c.acyclic
  -- The records that reach `l` through at least one link.
  let A : Digest → Finset SpecRec := fun l =>
    (c.raw.abs).filter fun x => ∃ k ∈ x.links, Reach hashSpec (c.raw.abs) {k} l
  intro l hl
  obtain ⟨n, hn⟩ : ∃ n, (A l).card = n := ⟨_, rfl⟩
  induction n using Nat.strong_induction_on generalizing l with
  | _ n ih =>
    by_cases hb : (c.reachSet (ls.flatMap fun l => ((c.get l).map (·.links)).getD #[])).contains l
    · rw [Std.ExtTreeSet.contains_iff_mem, mem_reachSet_code] at hb
      obtain ⟨-, k, hk, hR⟩ := hb
      obtain ⟨l', hl', hk'⟩ := Array.mem_flatMap.mp hk
      cases hy : c.get l' with
      | none => rw [hy] at hk'; simp at hk'
      | some y =>
        rw [hy] at hk'
        simp only [Option.map_some, Option.getD_some] at hk'
        have hRl : Reach hashSpec (c.raw.abs) {l'} l := reach_of_link c hy hk' hR
        obtain ⟨hy', rfl⟩ := (c.get_eq_some_iff).mp hy
        have hlt : (A (hashRecord y)).card < (A l).card := by
          apply Finset.card_lt_card
          rw [Finset.ssubset_iff_of_subset]
          · refine ⟨toSpec y, Finset.mem_filter.mpr ⟨hy', k, mem_toSpec_links.mpr hk', hR⟩, ?_⟩
            intro hmem
            obtain ⟨-, k', hk'', hR'⟩ := Finset.mem_filter.mp hmem
            exact hac _ hy' k' hk'' (by rw [hashSpec_toSpec]; exact hR')
          · intro x hx
            obtain ⟨hx, k', hk'', hR'⟩ := Finset.mem_filter.mp hx
            exact Finset.mem_filter.mpr ⟨hx, k', hk'', Reach.trans hashSpec hR' hRl⟩
        obtain ⟨m, hm, hRm⟩ := ih _ (hn ▸ hlt) _ hl' rfl
        exact ⟨m, hm, Reach.trans hashSpec hRm hRl⟩
    · refine ⟨l, Array.mem_filter.mpr ⟨hl, by simpa using Bool.eq_false_iff.mpr hb⟩,
      .head (Finset.mem_singleton_self _)⟩

/-- The newest records are records of the list. -/
theorem mem_of_mem_newestOf {c : ReadyStore} {ls : Array Digest} {n : Digest}
    (h : n ∈ newestOf c ls) : n ∈ ls :=
  (Array.mem_filter.mp h).1

/-- **What `viewOf` says reaches every live record**: for a non-empty list, `reachesAllLive` is
`some s`, and a stored digest is in `s` exactly when it reaches every record of the list. -/
theorem viewOf_reachesAllLive_spec (c : ReadyStore) (p : Array Digest × DigestSet)
    (hne : ∃ l, l ∈ p.1) (hst : ∀ l ∈ p.1, l ∈ c.raw.map) :
    ∃ s, (viewOf c p).reachesAllLive = some s ∧
      ∀ x ∈ c.raw.map, x ∈ s ↔ ∀ l ∈ p.1, Reach hashSpec (c.raw.abs) {x} l := by
  obtain ⟨hnone, hsome⟩ := reachersOfAll_spec (linkedByRaw c.raw) (newestOf c p.1)
  rw [viewOf_reachesAllLive]
  cases hr : reachersOfAll (linkedByRaw c.raw) (newestOf c p.1) with
  | none =>
    obtain ⟨l, hl⟩ := hne
    obtain ⟨n, hn, -⟩ := exists_newest c p.1 l hl
    rw [hnone.mp hr] at hn
    simp at hn
  | some s =>
    refine ⟨s, rfl, fun x hx => ?_⟩
    rw [hsome s hr x]
    constructor
    · intro h l hl
      obtain ⟨n, hn, hRn⟩ := exists_newest c p.1 l hl
      exact Reach.trans hashSpec
        ((mem_reachersOf c (hst n (mem_of_mem_newestOf hn))).mp (h n hn)).2 hRn
    · intro h n hn
      exact (mem_reachersOf c (hst n (mem_of_mem_newestOf hn))).mpr
        ⟨hx, h n (mem_of_mem_newestOf hn)⟩

/-! ## The author views, in the words of the spec -/

/-- Universal form of `exists_liveRecords`. -/
theorem forall_liveRecords {c : ReadyStore} {facts : Array Fact} {a : Aci}
    {Q : SpecRec → Prop} :
    (∀ y ∈ liveRecords hashSpec (c.raw.abs) (liveOf facts) a, Q y) ↔
      ∀ l x dis, (liveFacts facts)[l]? = some dis → c.get l = some x → x.author = a →
        Q (toSpec x) := by
  have := (exists_liveRecords (c := c) (facts := facts) (a := a) (Q := fun y => ¬ Q y)).not
  push Not at this
  exact this

/-- An author has no view exactly when they have no stored live record. -/
theorem authorViews_none (c : ReadyStore) (facts : Array Fact) (a : Aci) :
    (authorViewsRaw c.raw (liveFacts facts))[a]? = none ↔
      liveRecords hashSpec (c.raw.abs) (liveOf facts) a = ∅ := by
  have E := byAuthor_entry c (liveFacts facts) a
  rw [authorViews_eq, Std.ExtTreeMap.getElem?_map, Option.map_eq_none_iff,
    Finset.eq_empty_iff_forall_notMem]
  constructor
  · intro h y hy
    rw [h] at E
    obtain ⟨l, x, dis, hl, hx, ha, -⟩ :=
      (exists_liveRecords (Q := fun _ => True)).mp ⟨y, hy, trivial⟩
    exact E.1 l ⟨dis, x, hl, hx, ha⟩
  · intro h
    cases hb : (List.foldl (authorStep c) ∅ (liveFacts facts).toList)[a]? with
    | none => rfl
    | some p =>
      rw [hb] at E
      obtain ⟨-, -, l, dis, x, hl, hx, ha⟩ := E
      obtain ⟨y, hy, -⟩ := (exists_liveRecords (Q := fun _ => True)).mpr
        ⟨l, x, dis, hl, hx, ha, trivial⟩
      exact absurd hy (h y)

/-- **An author's view, in the words of the spec.** For a stored digest `d`: the view reaches
`d` exactly when one of the author's live records reaches it; it disowns `d` exactly when one of
them disowns it; and its `reachesAllLive` is `some s`, where `d` is in `s` exactly when `d`
reaches every live record of the author. -/
theorem authorViews_some (c : ReadyStore) (facts : Array Fact) {a : Aci} {v : AuthorView}
    (hv : (authorViewsRaw c.raw (liveFacts facts))[a]? = some v) {d : Digest} (hd : d ∈ c.raw.map) :
    (v.reach.contains d = true ↔ ∃ y ∈ liveRecords hashSpec (c.raw.abs) (liveOf facts) a,
      Reach hashSpec (c.raw.abs) {hashSpec y} d) ∧
    (v.disowned.contains d = true ↔ ∃ y ∈ liveRecords hashSpec (c.raw.abs) (liveOf facts) a,
      (hashSpec y, d) ∈ (liveOf facts).disown) ∧
    ∃ s, v.reachesAllLive = some s ∧ (s.contains d = true ↔
      ∀ y ∈ liveRecords hashSpec (c.raw.abs) (liveOf facts) a,
        Reach hashSpec (c.raw.abs) {d} (hashSpec y)) := by
  have E := byAuthor_entry c (liveFacts facts) a
  rw [authorViews_eq, Std.ExtTreeMap.getElem?_map] at hv
  obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.mp hv
  rw [hp] at E
  obtain ⟨h1, h2, l0, hl0⟩ := E
  have hget : ∀ l x, c.get l = some x → hashRecord x = l := fun l x hx =>
    ((c.get_eq_some_iff).mp hx).2
  refine ⟨?_, ?_, ?_⟩
  · show (c.reachSet p.1).contains d = true ↔ _
    rw [Std.ExtTreeSet.contains_iff_mem, mem_reachSet_code, exists_liveRecords]
    constructor
    · rintro ⟨-, k, hk, hR⟩
      obtain ⟨dis, x, hl, hx, ha⟩ := (h1 k).mp hk
      exact ⟨k, x, dis, hl, hx, ha, by rw [hashSpec_toSpec, hget k x hx]; exact hR⟩
    · rintro ⟨l, x, dis, hl, hx, ha, hR⟩
      rw [hashSpec_toSpec, hget l x hx] at hR
      exact ⟨hd, l, (h1 l).mpr ⟨dis, x, hl, hx, ha⟩, hR⟩
  · show p.2.contains d = true ↔ _
    rw [Std.ExtTreeSet.contains_iff_mem, h2, exists_liveRecords]
    constructor
    · rintro ⟨l, dis, x, hl, hx, ha, he⟩
      exact ⟨l, x, dis, hl, hx, ha, by
        rw [hashSpec_toSpec, hget l x hx, ← mem_liveFacts_disown hl]; exact he⟩
    · rintro ⟨l, x, dis, hl, hx, ha, he⟩
      rw [hashSpec_toSpec, hget l x hx, ← mem_liveFacts_disown hl] at he
      exact ⟨l, dis, x, hl, hx, ha, he⟩
  · obtain ⟨s, hs, hspec⟩ := viewOf_reachesAllLive_spec c p ⟨l0, (h1 l0).mpr hl0⟩
      (fun l hl => by
        obtain ⟨-, y, -, hy, -⟩ := (h1 l).mp hl
        exact Std.ExtTreeMap.mem_iff_isSome_getElem?.mpr (by
          rw [show c.raw.map[l]? = c.get l from rfl, hy]; rfl))
    refine ⟨s, hs, ?_⟩
    rw [Std.ExtTreeSet.contains_iff_mem, hspec d hd, forall_liveRecords]
    constructor
    · intro h l x dis hl hx ha
      rw [hashSpec_toSpec, hget l x hx]
      exact h l ((h1 l).mpr ⟨dis, x, hl, hx, ha⟩)
    · intro h l hl
      obtain ⟨dis, x, hld, hx, ha⟩ := (h1 l).mp hl
      have := h l x dis hld hx ha
      rwa [hashSpec_toSpec, hget l x hx] at this

/-- **The holders, read from the views**: `b` holds `r` exactly when `b` is not its author and
`b`'s view reaches `r`'s digest. -/
theorem mem_holders_iff (c : ReadyStore) (facts : Array Fact) {r : Rec} {d : Digest}
    (hd : hashRecord r = d) (hdm : d ∈ c.raw.map) (b : Aci) :
    b ∈ holders hashSpec (c.raw.abs) (liveOf facts) (toSpec r) ↔
      b ≠ r.author ∧ ∃ w, (authorViewsRaw c.raw (liveFacts facts))[b]? = some w ∧
        w.reach.contains d = true := by
  have hhr : hashSpec (toSpec r) = d := by rw [hashSpec_toSpec, hd]
  rw [holders, Finset.mem_image, hhr]
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨hx, hl, ha, hR⟩ := Finset.mem_filter.mp hx
    have hxl : x ∈ liveRecords hashSpec (c.raw.abs) (liveOf facts) x.author :=
      Finset.mem_filter.mpr ⟨hx, hl, rfl⟩
    cases hw : (authorViewsRaw c.raw (liveFacts facts))[x.author]? with
    | none =>
      rw [authorViews_none] at hw
      rw [hw] at hxl
      simp at hxl
    | some w =>
      exact ⟨ha, w, rfl, ((authorViews_some c facts hw hdm).1).mpr ⟨x, hxl, hR⟩⟩
  · rintro ⟨hne, w, hw, hR⟩
    obtain ⟨y, hy, hRy⟩ := ((authorViews_some c facts hw hdm).1).mp hR
    obtain ⟨hy, hl, ha⟩ := Finset.mem_filter.mp hy
    exact ⟨y, Finset.mem_filter.mpr ⟨hy, hl, ha ▸ hne, hRy⟩, ha⟩

/-! ## `classify` computes the spec's status -/

/-- **`status` computes the spec's status.** For a stored record `r` (under its digest `d`), the
status `classify` gives means exactly what the spec says (`StatusMeans`). -/
theorem status_spec (c : ReadyStore) (facts : Array Fact) {d : Digest} {r : Rec}
    (h : c.raw.map[d]? = some r) :
    StatusMeans (c.raw.abs) (liveOf facts) (toSpec r)
      (status (authorViewsRaw c.raw (liveFacts facts))
        (authorViewsRaw c.raw (liveFacts facts)).toList d r) := by
  have hd : hashRecord r = d := c.hash_eq d r h
  have hdm : d ∈ c.raw.map := Std.ExtTreeMap.mem_iff_isSome_getElem?.mpr (by simp [h])
  have hhr : hashSpec (toSpec r) = d := by rw [hashSpec_toSpec, hd]
  have hauth : (toSpec r).author = r.author := rfl
  -- "Held by" or "unconfirmed", when neither of the author's labels applies.
  have hHU : ¬ authorConfirmed hashSpec (c.raw.abs) (liveOf facts) (toSpec r) →
      ¬ foreignMarked hashSpec (c.raw.abs) (liveOf facts) (toSpec r) →
      StatusMeans (c.raw.abs) (liveOf facts) (toSpec r)
        (match List.find? (fun x => x.1 != r.author && Std.ExtTreeSet.contains x.2.reach d)
            (authorViewsRaw c.raw (liveFacts facts)).toList with
          | some (a, _) => Zrdt.Status.heldBy a
          | none => Zrdt.Status.unconfirmed) := by
    intro hAC hFM
    cases hf : List.find? (fun x => x.1 != r.author && Std.ExtTreeSet.contains x.2.reach d)
        (authorViewsRaw c.raw (liveFacts facts)).toList with
    | none =>
      refine ⟨hAC, hFM, ?_⟩
      rw [List.find?_eq_none] at hf
      apply Finset.eq_empty_of_forall_notMem
      intro b hb
      obtain ⟨hne, w, hw, hR⟩ := (mem_holders_iff c facts hd hdm b).mp hb
      apply hf (b, w) (Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some.mpr hw)
      simp [hne, hR]
    | some p =>
      obtain ⟨a, w⟩ := p
      obtain ⟨hp, as, bs, heq, has⟩ := List.find?_eq_some_iff_append.mp hf
      simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hp
      have haw : (a, w) ∈ (authorViewsRaw c.raw (liveFacts facts)).toList := by rw [heq]; simp
      have hw := Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some.mp haw
      refine ⟨hAC, hFM, (mem_holders_iff c facts hd hdm a).mpr ⟨hp.1, w, hw, hp.2⟩,
        fun b hb => ?_⟩
      obtain ⟨hne, w', hw', hR'⟩ := (mem_holders_iff c facts hd hdm b).mp hb
      have hbw := Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some.mpr hw'
      have hord := Std.ExtTreeMap.ordered_keys_toList (t := authorViewsRaw c.raw (liveFacts facts))
      rw [heq] at hbw hord
      rcases List.mem_append.mp hbw with hb' | hb'
      · have := has _ hb'
        simp [hne, hR'] at this
      · rcases List.mem_cons.mp hb' with he | hb'
        · cases he
          simp [Std.ReflCmp.compare_self]
        · rw [List.pairwise_append, List.pairwise_cons] at hord
          have := hord.2.1.1 _ hb'
          simp only at this
          rw [this]
          decide
  unfold status
  dsimp only
  cases hv : (authorViewsRaw c.raw (liveFacts facts))[r.author]? with
  | none =>
    have hLR := (authorViews_none c facts r.author).mp hv
    apply hHU
    · rintro ⟨⟨y, hy, -⟩, -⟩
      rw [hauth, hLR] at hy
      simp at hy
    · rintro (⟨y, hy, -⟩ | ⟨⟨y, hy, -⟩, -⟩) <;> (rw [hauth, hLR] at hy; simp at hy)
  | some v =>
    obtain ⟨eR, eD, s, hs, eS⟩ := authorViews_some c facts hv hdm
    have hAC : authorConfirmed hashSpec (c.raw.abs) (liveOf facts) (toSpec r) ↔
        v.reach.contains d = true ∧ ¬ v.disowned.contains d = true := by
      rw [authorConfirmed, hhr, hauth, eR, eD]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨h1, fun ⟨y, hy, he⟩ => h2 y hy he⟩
      · rintro ⟨h1, h2⟩
        exact ⟨h1, fun y hy he => h2 ⟨y, hy, he⟩⟩
    have hFM : foreignMarked hashSpec (c.raw.abs) (liveOf facts) (toSpec r) ↔
        v.disowned.contains d = true ∨
          (¬ s.contains d = true ∧ ¬ v.reach.contains d = true) := by
      rw [foreignMarked, hhr, hauth, eR, eD, eS]
      constructor
      · rintro (h1 | ⟨⟨y, hy, -, hny⟩, h2⟩)
        · exact Or.inl h1
        · exact Or.inr ⟨fun h => hny (h y hy), fun ⟨y', hy', hR⟩ => h2 y' hy' hR⟩
      · rintro (h1 | ⟨h1, h2⟩)
        · exact Or.inl h1
        · right
          push Not at h1
          obtain ⟨y, hy, hny⟩ := h1
          exact ⟨⟨y, hy, fun hR => h2 ⟨y, hy, hR⟩, hny⟩, fun y hy hR => h2 ⟨y, hy, hR⟩⟩
    dsimp only
    rw [hs]
    dsimp only
    generalize v.reach.contains d = RB at hAC hFM ⊢
    generalize v.disowned.contains d = DB at hAC hFM ⊢
    generalize s.contains d = SB at hFM ⊢
    cases RB <;> cases DB <;> cases SB <;>
      simp only [Bool.not_true, Bool.not_false, Bool.and_true, Bool.and_false, Bool.false_eq_true,
        ↓reduceIte] <;>
      simp only [Bool.false_eq_true, not_false_eq_true, not_true_eq_false, and_true, and_false,
        or_false, iff_true, iff_false, or_true] at hAC hFM <;>
      first
      | exact hAC
      | exact ⟨hAC, hFM⟩
      | exact hHU hAC hFM

/-- **`classify` computes the spec's status of every stored record, and of nothing else**, in
the words of `StatusMeans`. `ClassifyStatus.lean` turns this into the spec's `status`
(`classify_spec` below turns this into the spec's `status`; `Api.lean` advertises it for a
relative store as `RelStore.classify_spec`). -/
theorem classify_getElem?_iff (c : ReadyStore) (facts : Array Fact) (d : Digest)
    (st : Zrdt.Status) :
    (classifyRaw c.raw facts)[d]? = some st ↔
      ∃ r, c.get d = some r ∧ StatusMeans (c.raw.abs) (liveOf facts) (toSpec r) st := by
  rw [classifyRaw, Std.ExtTreeMap.getElem?_map]
  constructor
  · intro h
    obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.mp h
    exact ⟨r, hr, status_spec c facts hr⟩
  · rintro ⟨r, hr, hs⟩
    have hr' : c.raw.map[d]? = some r := hr
    rw [hr', Option.map_some, StatusMeans.unique (status_spec c facts hr') hs]


/-- **`classifyRaw` computes the spec's `status`** on a ready store: digest `d` gets the status
`st` exactly when `d` is the digest of a stored record `r` and the spec's `status` of `r` is
`st`. -/
theorem classify_spec (c : ReadyStore) (facts : Array Fact) (d : Digest) (st : Zrdt.Status) :
    (classifyRaw c.raw facts)[d]? = some st ↔
      ∃ r, c.raw.map[d]? = some r ∧
        Crdt.Merkle.status hashSpec c.raw.abs (liveOf facts) (toSpec r) = st.toSpec := by
  simp only [classify_getElem?_iff, statusMeans_iff_status]
  rfl

end ReadyStore

/-- **`CLASSIFY` on a relative store without a cycle computes the spec's `status`**: `classifyRaw`
(what `ChatStore.classify` runs on a relative store) gives digest `d` the status `st` exactly when
`d` is the digest of a stored record `r` and the spec's `status` of `r`, in the store's records,
is `st`. -/
theorem RelStore.classify_model (c : RelStore) (hac : Acyclic hashSpec c.raw.abs)
    (facts : Array Fact) (d : Digest) (st : Zrdt.Status) :
    (classifyRaw c.raw facts)[d]? = some st ↔
      ∃ r, c.get d = some r ∧
        Crdt.Merkle.status hashSpec c.raw.abs (liveOf facts) (toSpec r) = st.toSpec :=
  ReadyStore.classify_spec (.ofRel c hac) facts d st

/-- On a closed store, the ready-store statement is `CheckedStore.classify_eq_some_iff`. -/
example (c : CheckedStore) (facts : Array Fact) (d : Digest) (st : Zrdt.Status) :
    (classify c facts)[d]? = some st ↔
      ∃ r, c.get d = some r ∧
        Crdt.Merkle.status hashSpec (abs c) (liveOf facts) (toSpec r) = st.toSpec :=
  ReadyStore.classify_spec (.ofChecked c) facts d st

end Zrdt
