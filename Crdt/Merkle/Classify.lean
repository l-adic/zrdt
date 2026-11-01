/-
Copyright (c) 2026 zrdt contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: zrdt contributors
-/
import Mathlib
import Crdt.Merkle.Refine
import Zrdt.Provenance

set_option linter.unusedSectionVars false

/-!
# `CLASSIFY` in the spec model (docs/PLAN.md §3.2, §3.5)

`Zrdt.classify` gives each stored record a status from the host's facts (which records arrived
live, with their disown lists). The spec (`Crdt.Merkle`, `Chat.lean`) defines the same labels
from a store and `LiveFacts`: `authorConfirmed`, `foreignMarked` and `holders`, in that order of
precedence.

* `liveOf facts` is the spec's `LiveFacts` of the host's facts.
* `StatusMeans s P x st` says what the status `st` of record `x` means in the spec: exactly one
  status meets it. It is stated with the spec's three predicates, so it does not depend on how
  the spec's `Status` type carries "held by" (lane T5 changes it to one member, the smallest).
* `classifyRef_spec`: the literal reference `classifyRef` (the rules word for word) gives every
  stored record a status that means what the spec says.

TODO (next): `classify_eq_classifyRef` (the fast `classify` computes the same map as
`classifyRef`; checked on the examples in `Provenance.lean` and by a randomized comparison, not
yet proved). With it, `classify_spec` follows from `classifyRef_spec`.
-/

namespace Zrdt

open Crdt.Merkle

/-! ## Live facts -/

/-- The facts that say a record arrived live. -/
def liveList (facts : Array Fact) : List Fact :=
  facts.toList.filter fun f => f.provenance == .live

/-- **The spec's live facts** of the host's facts: the digests that some fact says arrived live,
and the pairs `(d, e)` where a live fact for `d` lists `e` in its disown list. -/
def liveOf (facts : Array Fact) : LiveFacts Digest where
  live := ((liveList facts).map (·.digest)).toFinset
  disown := ((liveList facts).flatMap fun f => f.disown.toList.map (f.digest, ·)).toFinset

example : liveOf #[] = ⟨∅, ∅⟩ := rfl
example : liveList #[⟨Examples.dig 1, .imported, #[]⟩] = [] := rfl

/-- A digest is live in `liveOf` exactly when some live fact is about it. -/
theorem mem_liveOf_live {facts : Array Fact} {d : Digest} :
    d ∈ (liveOf facts).live ↔ ∃ f ∈ facts, f.provenance = .live ∧ f.digest = d := by
  simp [liveOf, liveList, and_assoc]

/-- `(d, e)` is a disown pair of `liveOf` exactly when a live fact for `d` lists `e`. -/
theorem mem_liveOf_disown {facts : Array Fact} {d e : Digest} :
    (d, e) ∈ (liveOf facts).disown ↔
      ∃ f ∈ facts, f.provenance = .live ∧ f.digest = d ∧ e ∈ f.disown := by
  simp only [liveOf, liveList, List.mem_toFinset, List.mem_flatMap, List.mem_filter,
    Array.mem_toList_iff, beq_iff_eq, List.mem_map, Prod.mk.injEq]
  constructor
  · rintro ⟨f, ⟨hf, hl⟩, e', he', rfl, rfl⟩
    exact ⟨f, hf, hl, rfl, he'⟩
  · rintro ⟨f, hf, hl, rfl, he⟩
    exact ⟨f, ⟨hf, hl⟩, e, he, rfl, rfl⟩

/-- One step of `liveFacts`. -/
private def liveStep (m : Std.ExtTreeMap Digest (Array Digest) compare) (f : Fact) :
    Std.ExtTreeMap Digest (Array Digest) compare :=
  match f.provenance with
  | .live => m.insert f.digest (m.getD f.digest #[] ++ f.disown)
  | _ => m

/-- What folding `liveStep` over a list of facts does: a digest becomes a key when a live fact is
about it, and its disown list gains that fact's disown list. -/
private theorem foldl_liveStep (fs : List Fact) (m : Std.ExtTreeMap Digest (Array Digest) compare)
    (l : Digest) :
    (l ∈ fs.foldl liveStep m ↔ l ∈ m ∨ ∃ f ∈ fs, f.provenance = .live ∧ f.digest = l) ∧
    ∀ dis, (fs.foldl liveStep m)[l]? = some dis → ∀ e, e ∈ dis ↔
      (∃ d0, m[l]? = some d0 ∧ e ∈ d0) ∨
        ∃ f ∈ fs, f.provenance = .live ∧ f.digest = l ∧ e ∈ f.disown := by
  induction fs generalizing m with
  | nil =>
    refine ⟨by simp, fun dis h e => ?_⟩
    simp only [List.foldl_nil] at h
    simp [h]
  | cons f fs ih =>
    obtain ⟨ih1, ih2⟩ := ih (liveStep m f)
    simp only [List.foldl_cons]
    -- The step on `f`, by key and by value.
    have hmem : l ∈ liveStep m f ↔ l ∈ m ∨ (f.provenance = .live ∧ f.digest = l) := by
      unfold liveStep
      split
      · rename_i hp
        rw [Std.ExtTreeMap.mem_insert, Digest.compare_eq_iff]
        simp [hp, or_comm]
      · rename_i hp
        exact ⟨Or.inl, fun h => h.elim id fun h' => absurd h'.1 hp⟩
    have hval : ∀ e, (∃ d0, (liveStep m f)[l]? = some d0 ∧ e ∈ d0) ↔
        (∃ d0, m[l]? = some d0 ∧ e ∈ d0) ∨
          (f.provenance = .live ∧ f.digest = l ∧ e ∈ f.disown) := by
      intro e
      unfold liveStep
      split
      · rename_i hp
        rw [Std.ExtTreeMap.getElem?_insert]
        by_cases hl : f.digest = l
        · subst hl
          simp only [Digest.compare_self, ↓reduceIte, Option.some.injEq, exists_eq_left',
            Array.mem_append, Std.ExtTreeMap.getD_eq_getD_getElem?, hp, true_and]
          cases m[f.digest]? <;> simp
        · have hne : compare f.digest l ≠ .eq := by rw [Ne, Digest.compare_eq_iff]; exact hl
          simp [hne, hl]
      · rename_i hp
        exact ⟨Or.inl, fun h => h.elim id fun h' => absurd h'.1 hp⟩
    refine ⟨?_, fun dis hd e => ?_⟩
    · rw [ih1, hmem]
      constructor
      · rintro ((h | h) | ⟨g, hg, h⟩)
        · exact Or.inl h
        · exact Or.inr ⟨f, List.mem_cons_self, h⟩
        · exact Or.inr ⟨g, List.mem_cons_of_mem _ hg, h⟩
      · rintro (h | ⟨g, hg, h⟩)
        · exact Or.inl (Or.inl h)
        · rcases List.mem_cons.mp hg with rfl | hg
          · exact Or.inl (Or.inr h)
          · exact Or.inr ⟨g, hg, h⟩
    · rw [ih2 dis hd e, hval]
      constructor
      · rintro ((h | h) | ⟨g, hg, h⟩)
        · exact Or.inl h
        · exact Or.inr ⟨f, List.mem_cons_self, h⟩
        · exact Or.inr ⟨g, List.mem_cons_of_mem _ hg, h⟩
      · rintro (h | ⟨g, hg, h⟩)
        · exact Or.inl (Or.inl h)
        · rcases List.mem_cons.mp hg with rfl | hg
          · exact Or.inl (Or.inr h)
          · exact Or.inr ⟨g, hg, h⟩

/-- `liveFacts` is the fold of `liveStep`. -/
private theorem liveFacts_eq (facts : Array Fact) :
    liveFacts facts = facts.toList.foldl liveStep ∅ := by
  rw [liveFacts, ← Array.foldl_toList]
  rfl

/-- **`liveFacts` holds the live digests of `liveOf`.** -/
theorem mem_liveFacts {facts : Array Fact} {d : Digest} :
    d ∈ liveFacts facts ↔ d ∈ (liveOf facts).live := by
  rw [liveFacts_eq, (foldl_liveStep _ _ d).1, mem_liveOf_live]
  simp

/-- **`liveFacts` holds the disown pairs of `liveOf`.** -/
theorem mem_liveFacts_disown {facts : Array Fact} {d : Digest} {dis : Array Digest}
    (h : (liveFacts facts)[d]? = some dis) {e : Digest} :
    e ∈ dis ↔ (d, e) ∈ (liveOf facts).disown := by
  rw [liveFacts_eq] at h
  rw [(foldl_liveStep _ _ d).2 dis h e, mem_liveOf_disown]
  simp


/-! ## What a status means -/

/-- **What the status `st` of record `x` means** in the spec, in store `s` with live facts `P`.
The labels are tried in order, and the first that applies wins:

* `confirmedByAuthor`: `x` is confirmed by its author (`authorConfirmed`);
* `notConfirmedByAuthor`: not that, and `x` has the foreign marker (`foreignMarked`);
* `heldBy a`: neither, and `a` is the smallest member (byte order) whose live records reach `x`,
  among those who are not its author (`holders`);
* `unconfirmed`: none of these; no other member's live record reaches `x`.

Exactly one status meets this for each record (the order on account ids is total). -/
def StatusMeans (s : SpecStore) (P : LiveFacts Digest) (x : SpecRec) : Zrdt.Status → Prop
  | .confirmedByAuthor => authorConfirmed hashSpec s P x
  | .notConfirmedByAuthor => ¬ authorConfirmed hashSpec s P x ∧ foreignMarked hashSpec s P x
  | .heldBy a => ¬ authorConfirmed hashSpec s P x ∧ ¬ foreignMarked hashSpec s P x ∧
      a ∈ holders hashSpec s P x ∧ ∀ b ∈ holders hashSpec s P x, compare a b ≠ .gt
  | .unconfirmed => ¬ authorConfirmed hashSpec s P x ∧ ¬ foreignMarked hashSpec s P x ∧
      holders hashSpec s P x = ∅

-- With no live record at all, every record is `unconfirmed`, and only that.
example (x : SpecRec) : StatusMeans ∅ ⟨∅, ∅⟩ x .unconfirmed := by
  simp [StatusMeans, authorConfirmed, foreignMarked, holders, liveRecords]
example (x : SpecRec) : ¬ StatusMeans ∅ ⟨∅, ∅⟩ x .confirmedByAuthor := by
  simp [StatusMeans, authorConfirmed, liveRecords]

/-! ## The reference, in pieces -/

/-- The stored live records, each as (digest, record, disown list) (the `lives` of
`statusRef`). -/
def livesOf (c : CheckedStore) (live : Std.ExtTreeMap Digest (Array Digest) compare) :
    List (Digest × Rec × Array Digest) :=
  List.filterMap (fun x => Option.map (fun x_1 => (x.1, x_1, x.2)) (c.get x.1)) live.toList

example (c : CheckedStore) : livesOf c ∅ = [] := rfl

/-- The stored live records of `r`'s author (the `own` of `statusRef`). -/
def ownOf (c : CheckedStore) (live : Std.ExtTreeMap Digest (Array Digest) compare) (r : Rec) :
    List (Digest × Rec × Array Digest) :=
  (livesOf c live).filter fun x => x.2.1.author == r.author

example (c : CheckedStore) (r : Rec) : ownOf c ∅ r = [] := rfl

/-- `statusRef`'s decision, from its four inputs. -/
def statusOf (reached disowned parallel : Bool) (holders : List Aci) : Zrdt.Status :=
  if reached && !disowned then .confirmedByAuthor
  else if disowned || (parallel && !reached) then .notConfirmedByAuthor
  else
    match holders with
    | [] => .unconfirmed
    | a :: rest => .heldBy (rest.foldl minAci a)

example : statusOf true false false [] = .confirmedByAuthor := rfl

/-- `statusRef` is `statusOf` of its pieces. -/
theorem statusRef_eq (c : CheckedStore) (live : Std.ExtTreeMap Digest (Array Digest) compare)
    (d : Digest) (r : Rec) :
    statusRef c live d r = statusOf
      ((ownOf c live r).any fun x => reaches c x.1 d)
      ((ownOf c live r).any fun x => x.2.2.contains d)
      ((ownOf c live r).any fun x => !reaches c x.1 d && !reaches c d x.1)
      ((livesOf c live).filterMap fun x =>
        if (x.2.1.author != r.author && reaches c x.1 d) = true then some x.2.1.author else none) :=
  rfl

/-- A stored live record, in `livesOf`. -/
theorem mem_livesOf {c : CheckedStore} {live : Std.ExtTreeMap Digest (Array Digest) compare}
    {l : Digest} {y : Rec} {dis : Array Digest} :
    (l, y, dis) ∈ livesOf c live ↔ live[l]? = some dis ∧ c.get l = some y := by
  simp only [livesOf, List.mem_filterMap, Option.map_eq_some_iff, Prod.exists, Prod.mk.injEq]
  constructor
  · rintro ⟨l', dis', hl, y', hy, rfl, rfl, rfl⟩
    exact ⟨Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some.mp hl, hy⟩
  · rintro ⟨hl, hy⟩
    exact ⟨l, dis, Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some.mpr hl, y, hy, rfl, rfl, rfl⟩

/-- `any` over the stored live records of `r`'s author. -/
theorem any_ownOf {c : CheckedStore} {live : Std.ExtTreeMap Digest (Array Digest) compare}
    {r : Rec} (q : Digest × Rec × Array Digest → Bool) :
    (ownOf c live r).any q = true ↔
      ∃ l y dis, live[l]? = some dis ∧ c.get l = some y ∧ y.author = r.author ∧
        q (l, y, dis) = true := by
  simp only [ownOf, List.any_eq_true, List.mem_filter, Prod.exists, beq_iff_eq]
  constructor
  · rintro ⟨l, y, dis, ⟨hm, ha⟩, hq⟩
    exact ⟨l, y, dis, (mem_livesOf.mp hm).1, (mem_livesOf.mp hm).2, ha, hq⟩
  · rintro ⟨l, y, dis, hl, hy, ha, hq⟩
    exact ⟨l, y, dis, ⟨mem_livesOf.mpr ⟨hl, hy⟩, ha⟩, hq⟩

/-- The live records of author `a` in the spec, read as stored live records. -/
theorem exists_liveRecords {c : CheckedStore} {facts : Array Fact} {a : Aci}
    {Q : SpecRec → Prop} :
    (∃ y ∈ liveRecords hashSpec (abs c) (liveOf facts) a, Q y) ↔
      ∃ l x dis, (liveFacts facts)[l]? = some dis ∧ c.get l = some x ∧ x.author = a ∧
        Q (toSpec x) := by
  simp only [liveRecords, Finset.mem_filter]
  constructor
  · rintro ⟨y, ⟨hy, hl, ha⟩, hq⟩
    obtain ⟨x, rfl, hx⟩ := c.built.exists_of_mem_abs hy
    rw [hashSpec_toSpec, ← mem_liveFacts, Std.ExtTreeMap.mem_iff_isSome_getElem?,
      Option.isSome_iff_exists] at hl
    obtain ⟨dis, hdis⟩ := hl
    exact ⟨_, x, dis, hdis, hx, ha, hq⟩
  · rintro ⟨l, x, dis, hdis, hx, ha, hq⟩
    obtain ⟨hxs, rfl⟩ := (c.get_eq_some_iff).mp hx
    refine ⟨toSpec x, ⟨hxs, ?_, ha⟩, hq⟩
    rw [hashSpec_toSpec, ← mem_liveFacts, Std.ExtTreeMap.mem_iff_isSome_getElem?, hdis]
    rfl

/-- `reaches` is the spec's `Reach`, to a stored digest. -/
theorem reaches_iff (c : CheckedStore) {a b : Digest} (hb : b ∈ c.raw.map) :
    reaches c a b = true ↔ Reach hashSpec (abs c) {a} b := by
  have hs : (#[a] : Array Digest).toList.toFinset = {a} := by simp
  rw [reaches, Std.ExtTreeSet.contains_iff_mem, CheckedStore.reachSet_iff, hs, mem_digests]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ((mem_reachSet hashSpec).mp hy).2
  · intro hR
    obtain ⟨y, hy, rfl⟩ := (mem_digests hashSpec).mp (c.mem_digests_abs.mpr hb)
    exact ⟨y, (mem_reachSet hashSpec).mpr ⟨hy, hR⟩, rfl⟩

/-! ## The smallest account id -/

/-- Folding `minAci` gives one of the ids. -/
theorem foldl_minAci_mem (a : Aci) (rest : List Aci) : rest.foldl minAci a ∈ a :: rest := by
  induction rest generalizing a with
  | nil => simp
  | cons x rest ih =>
    rw [List.foldl_cons]
    have h := ih (minAci a x)
    have hm : minAci a x = a ∨ minAci a x = x := by unfold minAci; split <;> simp
    rcases List.mem_cons.mp h with h | h
    · rw [h]; rcases hm with hm | hm <;> rw [hm] <;> simp
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h)

/-- Folding `minAci` gives an id no bigger than any of them (byte order). -/
theorem foldl_minAci_le (a : Aci) (rest : List Aci) :
    ∀ b ∈ a :: rest, compare (rest.foldl minAci a) b ≠ .gt := by
  induction rest generalizing a with
  | nil =>
    intro b hb
    rw [List.mem_singleton] at hb
    subst hb
    simp [Std.ReflCmp.compare_self]
  | cons x rest ih =>
    rw [List.foldl_cons]
    have h := ih (minAci a x)
    have hle_a : compare (minAci a x) a ≠ .gt := by
      unfold minAci
      split
      · rename_i hgt
        rw [beq_iff_eq] at hgt
        rw [Std.OrientedCmp.gt_iff_lt.mp hgt]
        decide
      · simp [Std.ReflCmp.compare_self]
    have hle_x : compare (minAci a x) x ≠ .gt := by
      unfold minAci
      split
      · simp [Std.ReflCmp.compare_self]
      · rename_i hgt
        simpa using hgt
    intro b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · exact Std.TransCmp.le_trans (h _ List.mem_cons_self) hle_a
    rcases List.mem_cons.mp hb with rfl | hb
    · exact Std.TransCmp.le_trans (h _ List.mem_cons_self) hle_x
    · exact h b (List.mem_cons_of_mem _ hb)


/-! ## The reference computes the spec's status -/

/-- **`statusRef` computes the spec's status.** For a stored record `r` (under its digest `d`),
the status the literal reference gives means exactly what the spec says (`StatusMeans`), with the
spec's live facts read from the host's facts (`liveOf`). -/
theorem statusRef_spec (c : CheckedStore) (facts : Array Fact) {d : Digest} {r : Rec}
    (h : c.raw.map[d]? = some r) :
    StatusMeans (abs c) (liveOf facts) (toSpec r) (statusRef c (liveFacts facts) d r) := by
  have hd : hashRecord r = d := c.built.hash_eq d r h
  have hdm : d ∈ c.raw.map := Std.ExtTreeMap.mem_iff_isSome_getElem?.mpr (by simp [h])
  have hlm : ∀ l y, c.get l = some y → l ∈ c.raw.map := fun l y hy =>
    Std.ExtTreeMap.mem_iff_isSome_getElem?.mpr (by rw [CheckedStore.get] at hy; simp [hy])
  have hhash : ∀ l y, c.get l = some y → hashRecord y = l := fun l y hy =>
    ((c.get_eq_some_iff).mp hy).2
  have hauth : (toSpec r).author = r.author := rfl
  have hhr : hashSpec (toSpec r) = d := by rw [hashSpec_toSpec, hd]
  rw [statusRef_eq]
  generalize hRA : ((ownOf c (liveFacts facts) r).any fun x => reaches c x.1 d) = RA
  generalize hDIS : ((ownOf c (liveFacts facts) r).any fun x => x.2.2.contains d) = DIS
  generalize hPAR : ((ownOf c (liveFacts facts) r).any
    fun x => !reaches c x.1 d && !reaches c d x.1) = PAR
  generalize hH : ((livesOf c (liveFacts facts)).filterMap fun x =>
    if (x.2.1.author != r.author && reaches c x.1 d) = true then some x.2.1.author else none) = H
  -- The four inputs, in the words of the spec.
  have eRA : RA = true ↔ ∃ y ∈ liveRecords hashSpec (abs c) (liveOf facts) (toSpec r).author,
      Reach hashSpec (abs c) {hashSpec y} (hashSpec (toSpec r)) := by
    rw [← hRA, any_ownOf, exists_liveRecords, hauth, hhr]
    constructor
    · rintro ⟨l, y, dis, hl, hy, ha, hq⟩
      refine ⟨l, y, dis, hl, hy, ha, ?_⟩
      rw [hashSpec_toSpec, hhash l y hy]
      exact (reaches_iff c hdm).mp hq
    · rintro ⟨l, y, dis, hl, hy, ha, hq⟩
      refine ⟨l, y, dis, hl, hy, ha, ?_⟩
      rw [hashSpec_toSpec, hhash l y hy] at hq
      exact (reaches_iff c hdm).mpr hq
  have eDIS : DIS = true ↔ ∃ y ∈ liveRecords hashSpec (abs c) (liveOf facts) (toSpec r).author,
      (hashSpec y, hashSpec (toSpec r)) ∈ (liveOf facts).disown := by
    rw [← hDIS, any_ownOf, exists_liveRecords, hauth, hhr]
    constructor
    · rintro ⟨l, y, dis, hl, hy, ha, hq⟩
      refine ⟨l, y, dis, hl, hy, ha, ?_⟩
      rw [hashSpec_toSpec, hhash l y hy, ← mem_liveFacts_disown hl]
      simpa using hq
    · rintro ⟨l, y, dis, hl, hy, ha, hq⟩
      refine ⟨l, y, dis, hl, hy, ha, ?_⟩
      rw [hashSpec_toSpec, hhash l y hy, ← mem_liveFacts_disown hl] at hq
      simpa using hq
  have ePAR : PAR = true ↔ ∃ y ∈ liveRecords hashSpec (abs c) (liveOf facts) (toSpec r).author,
      ¬ Reach hashSpec (abs c) {hashSpec y} (hashSpec (toSpec r)) ∧
        ¬ Reach hashSpec (abs c) {hashSpec (toSpec r)} (hashSpec y) := by
    rw [← hPAR, any_ownOf, exists_liveRecords, hauth, hhr]
    constructor
    · rintro ⟨l, y, dis, hl, hy, ha, hq⟩
      refine ⟨l, y, dis, hl, hy, ha, ?_⟩
      rw [hashSpec_toSpec, hhash l y hy, ← reaches_iff c hdm, ← reaches_iff c (hlm l y hy)]
      simpa using hq
    · rintro ⟨l, y, dis, hl, hy, ha, hq⟩
      refine ⟨l, y, dis, hl, hy, ha, ?_⟩
      rw [hashSpec_toSpec, hhash l y hy, ← reaches_iff c hdm, ← reaches_iff c (hlm l y hy)] at hq
      simpa using hq
  have eH : ∀ a, a ∈ H ↔ a ∈ holders hashSpec (abs c) (liveOf facts) (toSpec r) := by
    intro a
    rw [← hH, holders, Finset.mem_image, hauth, hhr]
    simp only [List.mem_filterMap, Prod.exists, Finset.mem_filter]
    constructor
    · rintro ⟨l, y, dis, hm, hq⟩
      obtain ⟨hl, hy⟩ := mem_livesOf.mp hm
      split at hq
      · rename_i hc
        cases hq
        simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hc
        obtain ⟨hy', rfl⟩ := (c.get_eq_some_iff).mp hy
        refine ⟨toSpec y, ⟨hy', ?_, hc.1, ?_⟩, rfl⟩
        · rw [hashSpec_toSpec, ← mem_liveFacts, Std.ExtTreeMap.mem_iff_isSome_getElem?, hl]
          rfl
        · rw [hashSpec_toSpec]
          exact (reaches_iff c hdm).mp hc.2
      · cases hq
    · rintro ⟨x, ⟨hx, hl, ha, hR⟩, rfl⟩
      obtain ⟨y, rfl, hy⟩ := c.built.exists_of_mem_abs hx
      rw [hashSpec_toSpec, ← mem_liveFacts, Std.ExtTreeMap.mem_iff_isSome_getElem?,
        Option.isSome_iff_exists] at hl
      obtain ⟨dis, hdis⟩ := hl
      refine ⟨hashRecord y, y, dis, mem_livesOf.mpr ⟨hdis, hy⟩, ?_⟩
      rw [hashSpec_toSpec] at hR
      have hc : (y.author != r.author && reaches c (hashRecord y) d) = true := by
        simp only [Bool.and_eq_true, bne_iff_ne, ne_eq]
        exact ⟨ha, (reaches_iff c hdm).mpr hR⟩
      simp only [hc, ↓reduceIte]
      rfl
  -- The spec's labels, from the inputs.
  have hAC : authorConfirmed hashSpec (abs c) (liveOf facts) (toSpec r) ↔
      RA = true ∧ ¬ DIS = true := by
    rw [eRA, eDIS, authorConfirmed]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun ⟨y, hy, hd⟩ => h2 y hy hd⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun y hy hd => h2 ⟨y, hy, hd⟩⟩
  have hFM : foreignMarked hashSpec (abs c) (liveOf facts) (toSpec r) ↔
      DIS = true ∨ (PAR = true ∧ ¬ RA = true) := by
    rw [eRA, eDIS, ePAR, foreignMarked]
    constructor
    · rintro (h1 | ⟨h1, h2⟩)
      · exact Or.inl h1
      · exact Or.inr ⟨h1, fun ⟨y, hy, hR⟩ => h2 y hy hR⟩
    · rintro (h1 | ⟨h1, h2⟩)
      · exact Or.inl h1
      · exact Or.inr ⟨h1, fun y hy hR => h2 ⟨y, hy, hR⟩⟩
  unfold statusOf
  cases RA <;> cases DIS <;> cases PAR <;> simp only [hAC, hFM, StatusMeans] <;>
    simp only [Bool.false_eq_true, reduceIte, Bool.and_self, Bool.and_false, Bool.and_true,
      Bool.not_true, Bool.not_false, Bool.or_false, Bool.or_true, not_true_eq_false,
      not_false_eq_true, and_self, and_true, and_false, or_false, or_true, true_and]
  all_goals
    cases H with
    | nil =>
      ext a
      simp [← eH a]
    | cons a rest =>
      exact ⟨(eH _).mp (foldl_minAci_mem a rest), fun b hb =>
        foldl_minAci_le a rest b ((eH b).mpr hb)⟩


/-- Only one status means what the spec says, for a given record. -/
theorem StatusMeans.unique {s : SpecStore} {P : LiveFacts Digest} {x : SpecRec}
    {st st' : Zrdt.Status} (h : StatusMeans s P x st) (h' : StatusMeans s P x st') : st = st' := by
  cases st <;> cases st' <;> simp only [StatusMeans] at h h' <;>
    try first
    | rfl
    | (exfalso; tauto)
  · rename_i a b
    obtain ⟨-, -, ha, hle⟩ := h
    obtain ⟨-, -, hb, hle'⟩ := h'
    have h1 := hle b hb
    have h2 := hle' a ha
    rw [Std.OrientedCmp.eq_swap (cmp := (compare : Aci → Aci → Ordering))] at h2
    have : compare a b = .eq := by
      cases hc : compare a b <;> simp_all
    rw [Std.LawfulEqCmp.compare_eq_iff_eq] at this
    rw [this]
  · rename_i a
    obtain ⟨-, -, ha, -⟩ := h
    obtain ⟨-, -, he⟩ := h'
    rw [he] at ha
    exact absurd ha (Finset.notMem_empty a)
  · rename_i a
    obtain ⟨-, -, he⟩ := h
    obtain ⟨-, -, ha, -⟩ := h'
    rw [he] at ha
    exact absurd ha (Finset.notMem_empty a)

/-- **`classifyRef` computes the spec's status of every stored record, and of nothing else.**
`classifyRef c facts` gives digest `d` the status `st` exactly when `d` is the digest of a stored
record `r` and `st` means, for `r`, what the spec says (`StatusMeans`). -/
theorem classifyRef_spec (c : CheckedStore) (facts : Array Fact) (d : Digest) (st : Zrdt.Status) :
    (classifyRef c facts)[d]? = some st ↔
      ∃ r, c.get d = some r ∧ StatusMeans (abs c) (liveOf facts) (toSpec r) st := by
  rw [classifyRef, Std.ExtTreeMap.getElem?_map]
  constructor
  · intro h
    obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.mp h
    exact ⟨r, hr, statusRef_spec c facts hr⟩
  · rintro ⟨r, hr, hs⟩
    have hr' : c.raw.map[d]? = some r := hr
    rw [hr', Option.map_some, StatusMeans.unique (statusRef_spec c facts hr') hs]


example (c : CheckedStore) (facts : Array Fact) (d : Digest) (st : Zrdt.Status) :
    (classifyRef c facts)[d]? = some st ↔
      ∃ r, c.get d = some r ∧ StatusMeans (abs c) (liveOf facts) (toSpec r) st :=
  classifyRef_spec c facts d st

-- The empty store classifies nothing.
example (facts : Array Fact) (d : Digest) :
    (classifyRef (CheckedStore.empty Examples.group) facts)[d]? = none := by
  rw [classifyRef, Std.ExtTreeMap.getElem?_map]
  rfl

end Zrdt
