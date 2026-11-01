/-
Copyright (c) 2026 zrdt contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: zrdt contributors
-/
import Mathlib
import Crdt.Merkle.Classify

set_option linter.unusedSectionVars false

/-!
# The fast `classify` computes the spec's status (docs/PLAN.md §3.2, `classify_spec`)

`Classify.lean` shows that the literal reference `classifyRef` computes the spec's status. This
file shows the same for `classify`, the one `zrdtd` runs, step by step:

* accept-built stores with no collision have no cycles (`acyclic_of_acceptBuilt`);
* `linkedBy` holds, for each stored digest, the stored records that link it; `reachersOf` walks
  them backwards and finds exactly the records that reach a digest;
* `authorViews` holds, for each author with a stored live record, what those records reach, what
  they disown, and the records that reach all of them;
* `authors.find?` picks the smallest holder, as the authors are sorted.

`classify_getElem?_iff`: `classify` gives each stored record the status that means what the spec
says (`StatusMeans`), and gives nothing else a status. `classify_eq_classifyRef`: it computes the
same map as the literal reference.
-/

namespace Crdt.Merkle

variable {α H K : Type*} [DecidableEq α] [DecidableEq H] [DecidableEq K]
variable (hash : Record α H K → H)

/-! ## Reaching, and cycles -/

/-- Reaching is transitive: what `b` reaches, `a` reaches, if `a` reaches `b`. -/
theorem Reach.trans {s : Store α H K} {a b d : H} (hab : Reach hash s {a} b)
    (hbd : Reach hash s {b} d) : Reach hash s {a} d :=
  hbd.lift hash subset_rfl (fun x hx => by rw [Finset.mem_singleton] at hx; subst hx; exact hab)

/-- Reaching from a set is reaching from one of its members. -/
theorem reach_iff_exists {s : Store α H K} {S : Finset H} {d : H} :
    Reach hash s S d ↔ ∃ a ∈ S, Reach hash s {a} d := by
  constructor
  · intro h
    induction h with
    | head hd => exact ⟨_, hd, .head (Finset.mem_singleton_self _)⟩
    | link hr _ hl ih =>
      obtain ⟨a, ha, h⟩ := ih
      exact ⟨a, ha, .link hr h hl⟩
  · rintro ⟨a, ha, h⟩
    exact h.lift hash subset_rfl (fun x hx => by
      rw [Finset.mem_singleton] at hx; subst hx; exact .head ha)

/-- `s` has **no cycles**: following one or more links from a record never leads back to its own
hash. -/
def Acyclic (s : Store α H K) : Prop :=
  ∀ x ∈ s, ∀ k ∈ x.links, ¬ Reach hash s {k} (hash x)

example : Acyclic Toy.hash (∅ : Store ℕ ℕ Unit) := by simp [Acyclic]

/-- If no record of `insert r S` links `hash r`, then reaching from any other hash in
`insert r S` never passes through `r`: it is reaching in `S`. -/
private theorem reach_insert_of_unlinked {S : Store α H K} {r : Record α H K}
    (hun : ∀ y ∈ insert r S, hash r ∉ y.links) {k d : H} (hk : k ≠ hash r)
    (h : Reach hash (insert r S) {k} d) : Reach hash S {k} d ∧ d ≠ hash r := by
  induction h with
  | head hd =>
    rw [Finset.mem_singleton] at hd
    subst hd
    exact ⟨.head (Finset.mem_singleton_self _), hk⟩
  | @link y d hy _ hl ih =>
    obtain ⟨ih, hne⟩ := ih
    have hyS : y ∈ S := by
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact absurd rfl hne
      · exact hy
    exact ⟨.link hyS ih hl, fun he => hun y (Finset.mem_insert_of_mem hyS) (he ▸ hl)⟩

/-- Accepting a record keeps a closed store acyclic, if the result has no collision. -/
theorem acyclic_accept {S : Store α H K} (hc : Closed hash S) (ha : Acyclic hash S)
    (r : Record α H K) (hnc : ¬ CollisionIn hash (accept hash S r)) :
    Acyclic hash (accept hash S r) := by
  unfold accept at hnc ⊢
  split_ifs at hnc ⊢ with hl
  swap
  · exact ha
  by_cases hrS : r ∈ S
  · rwa [Finset.insert_eq_of_mem hrS]
  -- No record links `hash r`: such a link resolves in `S`, so `r` would collide with a record
  -- of `S`.
  have hun : ∀ y ∈ insert r S, hash r ∉ y.links := by
    intro y hy hlink
    have hd : hash r ∈ digests hash S := by
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact hl hlink
      · exact (mem_digests hash).mpr (hc y hy _ hlink)
    obtain ⟨y', hy', he⟩ := (mem_digests hash).mp hd
    have : y' = r := by
      by_contra hne
      exact hnc (CollisionIn.of_mem hash (Finset.mem_insert_of_mem hy')
        (Finset.mem_insert_self r S) hne he)
    exact hrS (this ▸ hy')
  intro x hx k hk hR
  have hkr : k ≠ hash r := fun he => hun x hx (he ▸ hk)
  obtain ⟨hR', hne⟩ := reach_insert_of_unlinked hash hun hkr hR
  rcases Finset.mem_insert.mp hx with rfl | hx
  · exact hne rfl
  · exact ha x hx k hk hR'

/-- **An accept-built store with no collision has no cycles.** -/
theorem acyclic_of_acceptBuilt {s : Store α H K} (hb : AcceptBuilt hash s)
    (hnc : ¬ CollisionIn hash s) : Acyclic hash s := by
  obtain ⟨l, -, hbuild⟩ := hb
  suffices ∀ (l : List (Record α H K)) (S : Store α H K), Closed hash S → Acyclic hash S →
      ¬ CollisionIn hash (l.foldl (accept hash) S) → Acyclic hash (l.foldl (accept hash) S) by
    rw [← hbuild]
    exact this l ∅ (closed_empty hash) (by simp [Acyclic]) (by rw [← hbuild] at hnc; exact hnc)
  intro l
  induction l with
  | nil => intro S _ ha _; exact ha
  | cons r l ih =>
    intro S hc ha hnc
    simp only [List.foldl_cons] at hnc ⊢
    apply ih _ (closed_accept hash hc r) _ hnc
    exact acyclic_accept hash hc ha r fun h =>
      hnc (CollisionIn.mono hash (subset_foldl_accept hash l _) h)

end Crdt.Merkle

namespace Zrdt

open Crdt.Merkle

/-! ## Links followed backwards -/

/-- `WalkReach` is transitive. -/
theorem WalkReach.trans {β : Type} {m : Std.ExtTreeMap Digest β compare} {next : β → List Digest}
    {a b x : Digest} (hab : WalkReach m next [a] b) (hbx : WalkReach m next [b] x) :
    WalkReach m next [a] x := by
  induction hbx with
  | start hd => rw [List.mem_singleton] at hd; subst hd; exact hab
  | step _ hk hd ih => exact .step ih hk hd

/-- One step of `linkedBy`: record `p.2`, stored under `p.1`, is added to the list of each of its
links. -/
def linkStep (m : Std.ExtTreeMap Digest (List Digest) compare) (p : Digest × Rec) :
    Std.ExtTreeMap Digest (List Digest) compare :=
  p.2.links.foldl (init := m) fun m l => m.modify l (p.1 :: ·)

example : linkStep ∅ (Examples.dig 1, Examples.first) = ∅ := rfl

/-- `linkedBy` is the fold of `linkStep` over the stored records. -/
theorem linkedBy_eq (c : CheckedStore) :
    linkedBy c = c.raw.map.toList.foldl linkStep (c.raw.map.map fun _ _ => []) := by
  rw [linkedBy, Std.ExtTreeMap.foldl_eq_foldl_toList]
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
theorem mem_linkedBy (c : CheckedStore) {k : Digest} : k ∈ linkedBy c ↔ k ∈ c.raw.map := by
  rw [linkedBy_eq, (foldl_linkStep _ _ k).1, Std.ExtTreeMap.mem_map]

/-- **`linkedBy` lists exactly the stored records that link a digest.** -/
theorem linkedBy_get (c : CheckedStore) {k : Digest} {v : List Digest}
    (h : (linkedBy c)[k]? = some v) {x : Digest} :
    x ∈ v ↔ ∃ y, c.raw.map[x]? = some y ∧ k ∈ y.links := by
  rw [linkedBy_eq] at h
  obtain ⟨v0, hv0, hx⟩ := (foldl_linkStep _ _ k).2 v h
  rw [Std.ExtTreeMap.getElem?_map] at hv0
  obtain ⟨_, -, rfl⟩ := Option.map_eq_some_iff.mp hv0
  rw [hx x]
  simp only [List.not_mem_nil, false_or, Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some]

/-- **`reachersOf` finds exactly the stored records that reach `d`.** -/
theorem mem_reachersOf (c : CheckedStore) {d x : Digest} :
    x ∈ reachersOf (linkedBy c) d ↔ x ∈ c.raw.map ∧ Reach hashSpec (abs c) {x} d := by
  rw [reachersOf, mem_walk_iff, mem_linkedBy]
  refine and_congr_right fun hx => ⟨fun h => ?_, fun h => ?_⟩
  · clear hx
    induction h with
    | start hd => rw [List.mem_singleton] at hd; subst hd; exact .head (Finset.mem_singleton_self _)
    | @step k x v _ hk hxv ih =>
      obtain ⟨y, hy, hky⟩ := (linkedBy_get c hk).mp hxv
      have hxy : hashRecord y = x := c.built.hash_eq x y hy
      refine Reach.trans hashSpec ?_ ih
      refine .link (r := toSpec y) (RawStore.mem_abs.mpr ⟨x, y, hy, rfl⟩) ?_
        (mem_toSpec_links.mpr hky)
      rw [hashSpec_toSpec, hxy]
      exact .head (Finset.mem_singleton_self _)
  · induction h with
    | head hd => rw [Finset.mem_singleton] at hd; subst hd; exact .start List.mem_cons_self
    | @link y d' hy _ hl ih =>
      obtain ⟨r, rfl, hr⟩ := c.built.exists_of_mem_abs hy
      rw [hashSpec_toSpec] at ih
      have hl' : d' ∈ r.links := mem_toSpec_links.mp hl
      have hd' : d' ∈ c.raw.map := c.built.closed _ r hr d' hl'
      obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp
        (Std.ExtTreeMap.mem_iff_isSome_getElem?.mp ((mem_linkedBy c).mpr hd'))
      have hrv : hashRecord r ∈ v := (linkedBy_get c hv).mpr ⟨r, hr, hl'⟩
      exact WalkReach.trans (.step (.start List.mem_cons_self) hv hrv) ih

/-! ## Records that reach every one of a list -/

/-- One step of `reachersOfAll`. -/
def allStep (back : Std.ExtTreeMap Digest (List Digest) compare) (acc : Option DigestSet)
    (m : Digest) : Option DigestSet :=
  some (match acc with
    | none => reachersOf back m
    | some s => s.filter ((reachersOf back m).contains ·))

example : (allStep ∅ none (Examples.dig 1)).isSome = true := rfl

/-- `reachersOfAll` is the fold of `allStep`. -/
theorem reachersOfAll_eq (back : Std.ExtTreeMap Digest (List Digest) compare)
    (ns : Array Digest) : reachersOfAll back ns = ns.toList.foldl (allStep back) none := by
  rw [reachersOfAll, Array.foldl_toList]
  rfl

private theorem foldl_allStep (back : Std.ExtTreeMap Digest (List Digest) compare)
    (ms : List Digest) (acc : Option DigestSet) :
    (ms.foldl (allStep back) acc = none ↔ acc = none ∧ ms = []) ∧
    ∀ s, ms.foldl (allStep back) acc = some s → ∀ x, x ∈ s ↔
      (∀ s0, acc = some s0 → x ∈ s0) ∧ ∀ m ∈ ms, x ∈ reachersOf back m := by
  induction ms generalizing acc with
  | nil =>
    refine ⟨by simp, fun s h x => ?_⟩
    simp only [List.foldl_nil] at h
    subst h
    simp
  | cons m ms ih =>
    obtain ⟨-, ih2⟩ := ih (allStep back acc m)
    simp only [List.foldl_cons]
    refine ⟨?_, fun s h x => ?_⟩
    · constructor
      · intro h
        cases hs : List.foldl (allStep back) (allStep back acc m) ms with
        | none =>
          have := (ih (allStep back acc m)).1.mp hs
          simp [allStep] at this
        | some _ => rw [hs] at h; cases h
      · rintro ⟨-, h⟩; cases h
    · rw [ih2 s h x]
      have hstep : ∀ s1, allStep back acc m = some s1 → (x ∈ s1 ↔
          (∀ s0, acc = some s0 → x ∈ s0) ∧ x ∈ reachersOf back m) := by
        intro s1 hs1
        unfold allStep at hs1
        cases acc with
        | none =>
          cases hs1
          simp
        | some s0 =>
          cases hs1
          rw [Std.ExtTreeSet.mem_filter]
          constructor
          · rintro ⟨hx, hc⟩
            rw [Std.ExtTreeSet.get_eq] at hc
            exact ⟨fun s0' he => by cases he; exact hx,
              Std.ExtTreeSet.contains_iff_mem.mp hc⟩
          · rintro ⟨hx, hc⟩
            have hx' := hx s0 rfl
            exact ⟨hx', by rw [Std.ExtTreeSet.get_eq]; exact Std.ExtTreeSet.contains_iff_mem.mpr hc⟩
      constructor
      · rintro ⟨h1, h2⟩
        have := (hstep _ rfl).mp (h1 _ rfl)
        exact ⟨this.1, fun m' hm' => by
          rcases List.mem_cons.mp hm' with rfl | hm'
          · exact this.2
          · exact h2 m' hm'⟩
      · rintro ⟨h1, h2⟩
        refine ⟨fun s1 hs1 => (hstep s1 hs1).mpr ⟨h1, h2 m List.mem_cons_self⟩,
          fun m' hm' => h2 m' (List.mem_cons_of_mem _ hm')⟩

/-- **`reachersOfAll`**: `none` exactly for an empty list; otherwise the records that are in
`reachersOf back m` for every `m` of the list. -/
theorem reachersOfAll_spec (back : Std.ExtTreeMap Digest (List Digest) compare)
    (ns : Array Digest) :
    (reachersOfAll back ns = none ↔ ns = #[]) ∧
    ∀ s, reachersOfAll back ns = some s → ∀ x, x ∈ s ↔ ∀ m ∈ ns, x ∈ reachersOf back m := by
  rw [reachersOfAll_eq]
  obtain ⟨h1, h2⟩ := foldl_allStep back ns.toList none
  refine ⟨by rw [h1]; simp, fun s h x => ?_⟩
  rw [h2 s h x]
  simp

/-! ## The author views -/

/-- Inserting the digests of a list into a set. -/
theorem mem_foldl_insert (dis : List Digest) (ds : DigestSet) (e : Digest) :
    e ∈ dis.foldl (fun s x => s.insert x) ds ↔ e ∈ ds ∨ e ∈ dis := by
  induction dis generalizing ds with
  | nil => simp
  | cons x dis ih =>
    rw [List.foldl_cons, ih, Std.ExtTreeSet.mem_insert, Digest.compare_eq_iff, List.mem_cons]
    tauto

/-- One step of the `byAuthor` fold in `authorViews`. -/
def authorStep (c : CheckedStore) (m : Std.ExtTreeMap Aci (Array Digest × DigestSet) compare)
    (p : Digest × Array Digest) : Std.ExtTreeMap Aci (Array Digest × DigestSet) compare :=
  match c.get p.1 with
  | some r =>
    let (ls, ds) := m.getD r.author (#[], ∅)
    m.insert r.author (ls.push p.1, p.2.foldl (fun s x => s.insert x) ds)
  | none => m

/-- The view of one author, from its live digests `ls` and disowned digests `ds`. -/
def viewOf (c : CheckedStore) (p : Array Digest × DigestSet) : AuthorView :=
  let below := c.reachSet (p.1.flatMap fun l => ((c.get l).map (·.links)).getD #[])
  let newest := p.1.filter (!below.contains ·)
  ⟨c.reachSet p.1, p.2, reachersOfAll (linkedBy c) newest⟩

/-- `authorViews` is `viewOf` on the fold of `authorStep`. -/
theorem authorViews_eq (c : CheckedStore) (live : Std.ExtTreeMap Digest (Array Digest) compare) :
    authorViews c live = (live.toList.foldl (authorStep c) ∅).map fun _ p => viewOf c p := by
  rw [authorViews, Std.ExtTreeMap.foldl_eq_foldl_toList]
  rfl

/-- What the `byAuthor` entry of one author holds: no entry when `L` holds for no digest;
otherwise the live digests are exactly those where `L` holds (there is one), and the disowned
digests exactly those where `E` holds. -/
def EntryIs (o : Option (Array Digest × DigestSet)) (L E : Digest → Prop) : Prop :=
  match o with
  | none => (∀ l, ¬ L l) ∧ ∀ e, ¬ E e
  | some p => (∀ l, l ∈ p.1 ↔ L l) ∧ (∀ e, e ∈ p.2 ↔ E e) ∧ ∃ l, L l

example : EntryIs none (fun _ => False) (fun _ => False) := ⟨fun _ h => h, fun _ h => h⟩

/-- `EntryIs` only depends on what `L` and `E` hold for. -/
theorem EntryIs.congr {o : Option (Array Digest × DigestSet)} {L E L' E' : Digest → Prop}
    (h : EntryIs o L E) (hL : ∀ l, L l ↔ L' l) (hE : ∀ e, E e ↔ E' e) : EntryIs o L' E' := by
  cases o with
  | none => exact ⟨fun l => by rw [← hL]; exact h.1 l, fun e => by rw [← hE]; exact h.2 e⟩
  | some p =>
    obtain ⟨h1, h2, l, hl⟩ := h
    exact ⟨fun l => (h1 l).trans (hL l), fun e => (h2 e).trans (hE e), l, (hL l).mp hl⟩

/-- One `authorStep`, for author `a`. -/
theorem EntryIs.step (c : CheckedStore) {m : Std.ExtTreeMap Aci (Array Digest × DigestSet) compare}
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
theorem EntryIs.foldl (c : CheckedStore) (ps : List (Digest × Array Digest))
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
    refine (ih (h.step c p)).congr (fun l => ?_) (fun e => ?_)
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
theorem byAuthor_entry (c : CheckedStore) (live : Std.ExtTreeMap Digest (Array Digest) compare)
    (a : Aci) :
    EntryIs (live.toList.foldl (authorStep c) ∅)[a]?
      (fun l => ∃ dis y, live[l]? = some dis ∧ c.get l = some y ∧ y.author = a)
      (fun e => ∃ l dis y, live[l]? = some dis ∧ c.get l = some y ∧ y.author = a ∧ e ∈ dis) := by
  have h0 : EntryIs (∅ : Std.ExtTreeMap Aci (Array Digest × DigestSet) compare)[a]?
      (fun _ => False) (fun _ => False) := by
    rw [Std.ExtTreeMap.getElem?_empty]; exact ⟨fun _ h => h, fun _ h => h⟩
  refine (EntryIs.foldl c live.toList h0).congr (fun l => ?_) (fun e => ?_)
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
theorem mem_reachSet_code (c : CheckedStore) (S : Array Digest) {x : Digest} :
    x ∈ c.reachSet S ↔ x ∈ c.raw.map ∧ ∃ k ∈ S, Reach hashSpec (abs c) {k} x := by
  rw [CheckedStore.reachSet_iff, mem_digests]
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨hy, hR⟩ := (mem_reachSet hashSpec).mp hy
    obtain ⟨k, hk, hR⟩ := (reach_iff_exists hashSpec).mp hR
    exact ⟨c.mem_digests_abs.mp ((mem_digests hashSpec).mpr ⟨y, hy, rfl⟩), k,
      Array.mem_toList_iff.mp (List.mem_toFinset.mp hk), hR⟩
  · rintro ⟨hx, k, hk, hR⟩
    obtain ⟨y, hy, rfl⟩ := (mem_digests hashSpec).mp (c.mem_digests_abs.mpr hx)
    refine ⟨y, (mem_reachSet hashSpec).mpr ⟨hy, ?_⟩, rfl⟩
    exact (reach_iff_exists hashSpec).mpr ⟨k, List.mem_toFinset.mpr (Array.mem_toList_iff.mpr hk), hR⟩

/-- The live records of a list that no other of them reaches through a link (the `newest` of
`authorViews`). -/
def newestOf (c : CheckedStore) (ls : Array Digest) : Array Digest :=
  ls.filter (!(c.reachSet (ls.flatMap fun l => ((c.get l).map (·.links)).getD #[])).contains ·)

/-- `viewOf`'s third field is `reachersOfAll` of the newest records. -/
theorem viewOf_reachesAllLive (c : CheckedStore) (p : Array Digest × DigestSet) :
    (viewOf c p).reachesAllLive = reachersOfAll (linkedBy c) (newestOf c p.1) := rfl

/-- A stored record reaches `l` if it reaches a link of the record stored under `l`. -/
theorem reach_of_link (c : CheckedStore) {l k x : Digest} {y : Rec} (hy : c.get l = some y)
    (hk : k ∈ y.links) (hR : Reach hashSpec (abs c) {k} x) : Reach hashSpec (abs c) {l} x := by
  obtain ⟨hy', rfl⟩ := (c.get_eq_some_iff).mp hy
  refine Reach.trans hashSpec ?_ hR
  refine .link hy' ?_ (mem_toSpec_links.mpr hk)
  rw [hashSpec_toSpec]
  exact .head (Finset.mem_singleton_self _)

/-- **Every record of the list is reached from a newest one**, since a store has no cycles. -/
theorem exists_newest (c : CheckedStore) (ls : Array Digest) :
    ∀ l ∈ ls, ∃ n ∈ newestOf c ls, Reach hashSpec (abs c) {n} l := by
  classical
  have hac : Acyclic hashSpec (abs c) := acyclic_of_acceptBuilt hashSpec c.acceptBuilt c.built.no_collision
  -- The records that reach `l` through at least one link.
  let A : Digest → Finset SpecRec := fun l =>
    (abs c).filter fun x => ∃ k ∈ x.links, Reach hashSpec (abs c) {k} l
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
        have hRl : Reach hashSpec (abs c) {l'} l := reach_of_link c hy hk' hR
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
theorem mem_of_mem_newestOf {c : CheckedStore} {ls : Array Digest} {n : Digest}
    (h : n ∈ newestOf c ls) : n ∈ ls :=
  (Array.mem_filter.mp h).1

/-- **What `viewOf` says reaches every live record**: for a non-empty list, `reachesAllLive` is
`some s`, and a stored digest is in `s` exactly when it reaches every record of the list. -/
theorem viewOf_reachesAllLive_spec (c : CheckedStore) (p : Array Digest × DigestSet)
    (hne : ∃ l, l ∈ p.1) : ∃ s, (viewOf c p).reachesAllLive = some s ∧
      ∀ x ∈ c.raw.map, x ∈ s ↔ ∀ l ∈ p.1, Reach hashSpec (abs c) {x} l := by
  obtain ⟨hnone, hsome⟩ := reachersOfAll_spec (linkedBy c) (newestOf c p.1)
  rw [viewOf_reachesAllLive]
  cases hr : reachersOfAll (linkedBy c) (newestOf c p.1) with
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
      exact Reach.trans hashSpec ((mem_reachersOf c).mp (h n hn)).2 hRn
    · intro h n hn
      exact (mem_reachersOf c).mpr ⟨hx, h n (mem_of_mem_newestOf hn)⟩

/-! ## The author views, in the words of the spec -/

/-- Universal form of `exists_liveRecords`. -/
theorem forall_liveRecords {c : CheckedStore} {facts : Array Fact} {a : Aci}
    {Q : SpecRec → Prop} :
    (∀ y ∈ liveRecords hashSpec (abs c) (liveOf facts) a, Q y) ↔
      ∀ l x dis, (liveFacts facts)[l]? = some dis → c.get l = some x → x.author = a →
        Q (toSpec x) := by
  have := (exists_liveRecords (c := c) (facts := facts) (a := a) (Q := fun y => ¬ Q y)).not
  push Not at this
  exact this

/-- An author has no view exactly when they have no stored live record. -/
theorem authorViews_none (c : CheckedStore) (facts : Array Fact) (a : Aci) :
    (authorViews c (liveFacts facts))[a]? = none ↔
      liveRecords hashSpec (abs c) (liveOf facts) a = ∅ := by
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
theorem authorViews_some (c : CheckedStore) (facts : Array Fact) {a : Aci} {v : AuthorView}
    (hv : (authorViews c (liveFacts facts))[a]? = some v) {d : Digest} (hd : d ∈ c.raw.map) :
    (v.reach.contains d = true ↔ ∃ y ∈ liveRecords hashSpec (abs c) (liveOf facts) a,
      Reach hashSpec (abs c) {hashSpec y} d) ∧
    (v.disowned.contains d = true ↔ ∃ y ∈ liveRecords hashSpec (abs c) (liveOf facts) a,
      (hashSpec y, d) ∈ (liveOf facts).disown) ∧
    ∃ s, v.reachesAllLive = some s ∧ (s.contains d = true ↔
      ∀ y ∈ liveRecords hashSpec (abs c) (liveOf facts) a, Reach hashSpec (abs c) {d} (hashSpec y)) := by
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
theorem mem_holders_iff (c : CheckedStore) (facts : Array Fact) {r : Rec} {d : Digest}
    (hd : hashRecord r = d) (hdm : d ∈ c.raw.map) (b : Aci) :
    b ∈ holders hashSpec (abs c) (liveOf facts) (toSpec r) ↔
      b ≠ r.author ∧ ∃ w, (authorViews c (liveFacts facts))[b]? = some w ∧
        w.reach.contains d = true := by
  have hhr : hashSpec (toSpec r) = d := by rw [hashSpec_toSpec, hd]
  rw [holders, Finset.mem_image, hhr]
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨hx, hl, ha, hR⟩ := Finset.mem_filter.mp hx
    have hxl : x ∈ liveRecords hashSpec (abs c) (liveOf facts) x.author :=
      Finset.mem_filter.mpr ⟨hx, hl, rfl⟩
    cases hw : (authorViews c (liveFacts facts))[x.author]? with
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
theorem status_spec (c : CheckedStore) (facts : Array Fact) {d : Digest} {r : Rec}
    (h : c.raw.map[d]? = some r) :
    StatusMeans (abs c) (liveOf facts) (toSpec r)
      (status (authorViews c (liveFacts facts)) (authorViews c (liveFacts facts)).toList d r) := by
  have hd : hashRecord r = d := c.built.hash_eq d r h
  have hdm : d ∈ c.raw.map := Std.ExtTreeMap.mem_iff_isSome_getElem?.mpr (by simp [h])
  have hhr : hashSpec (toSpec r) = d := by rw [hashSpec_toSpec, hd]
  have hauth : (toSpec r).author = r.author := rfl
  -- "Held by" or "unconfirmed", when neither of the author's labels applies.
  have hHU : ¬ authorConfirmed hashSpec (abs c) (liveOf facts) (toSpec r) →
      ¬ foreignMarked hashSpec (abs c) (liveOf facts) (toSpec r) →
      StatusMeans (abs c) (liveOf facts) (toSpec r)
        (match List.find? (fun x => x.1 != r.author && Std.ExtTreeSet.contains x.2.reach d)
            (authorViews c (liveFacts facts)).toList with
          | some (a, _) => Zrdt.Status.heldBy a
          | none => Zrdt.Status.unconfirmed) := by
    intro hAC hFM
    cases hf : List.find? (fun x => x.1 != r.author && Std.ExtTreeSet.contains x.2.reach d)
        (authorViews c (liveFacts facts)).toList with
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
      have haw : (a, w) ∈ (authorViews c (liveFacts facts)).toList := by rw [heq]; simp
      have hw := Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some.mp haw
      refine ⟨hAC, hFM, (mem_holders_iff c facts hd hdm a).mpr ⟨hp.1, w, hw, hp.2⟩,
        fun b hb => ?_⟩
      obtain ⟨hne, w', hw', hR'⟩ := (mem_holders_iff c facts hd hdm b).mp hb
      have hbw := Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some.mpr hw'
      have hord := Std.ExtTreeMap.ordered_keys_toList (t := authorViews c (liveFacts facts))
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
  cases hv : (authorViews c (liveFacts facts))[r.author]? with
  | none =>
    have hLR := (authorViews_none c facts r.author).mp hv
    apply hHU
    · rintro ⟨⟨y, hy, -⟩, -⟩
      rw [hauth, hLR] at hy
      simp at hy
    · rintro (⟨y, hy, -⟩ | ⟨⟨y, hy, -⟩, -⟩) <;> (rw [hauth, hLR] at hy; simp at hy)
  | some v =>
    obtain ⟨eR, eD, s, hs, eS⟩ := authorViews_some c facts hv hdm
    have hAC : authorConfirmed hashSpec (abs c) (liveOf facts) (toSpec r) ↔
        v.reach.contains d = true ∧ ¬ v.disowned.contains d = true := by
      rw [authorConfirmed, hhr, hauth, eR, eD]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨h1, fun ⟨y, hy, he⟩ => h2 y hy he⟩
      · rintro ⟨h1, h2⟩
        exact ⟨h1, fun y hy he => h2 ⟨y, hy, he⟩⟩
    have hFM : foreignMarked hashSpec (abs c) (liveOf facts) (toSpec r) ↔
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

/-- **`classify` computes the spec's status of every stored record, and of nothing else**
(advertised as `CheckedStore.classify_spec` in `Api.lean`). -/
theorem classify_getElem?_iff (c : CheckedStore) (facts : Array Fact) (d : Digest)
    (st : Zrdt.Status) :
    (classify c facts)[d]? = some st ↔
      ∃ r, c.get d = some r ∧ StatusMeans (abs c) (liveOf facts) (toSpec r) st := by
  rw [classify, Std.ExtTreeMap.getElem?_map]
  constructor
  · intro h
    obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.mp h
    exact ⟨r, hr, status_spec c facts hr⟩
  · rintro ⟨r, hr, hs⟩
    have hr' : c.raw.map[d]? = some r := hr
    rw [hr', Option.map_some, StatusMeans.unique (status_spec c facts hr') hs]

/-- The fast `classify` and the literal reference `classifyRef` give the same map. -/
theorem classify_eq_classifyRef (c : CheckedStore) (facts : Array Fact) :
    classify c facts = classifyRef c facts := by
  apply Std.ExtTreeMap.ext_getElem?
  intro d
  apply Option.ext
  intro st
  rw [classify_getElem?_iff, classifyRef_spec]

example (c : CheckedStore) : classify c #[] = classifyRef c #[] := classify_eq_classifyRef c #[]

end Zrdt
