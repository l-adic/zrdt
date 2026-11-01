/-
Copyright (c) 2026 zrdt contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: zrdt contributors
-/
import Mathlib
import Crdt.Merkle.Defs
import Crdt.Merkle.Chat

set_option linter.unusedSectionVars false

/-!
# Relative stores: a newcomer's view with an opaque boundary

A member added to a group with history gets the records he was sent, the records written after
those, and only the digests of the older records they link (`docs/JOIN_PLAN.md` §6). So his store
is a **view** `(F, B)`: full records `F`, and **boundary** digests `B`. A boundary digest is a
leaf: the view does not know what it links. A closed store `s` is the view `(s, ∅)`.

A responder may itself be a former newcomer, with a relative store `(S, BS)`. For a requester who
may see the records `vis`, it serves the view `(servedF S vis, servedB' S vis BS)`: its records
that reach a `vis` record, and as boundary the other digests of its view that those records link,
and its other heads.

* `served_heads'`: the served view has exactly the responder's heads, for any `vis`. There is no
  collision clause. So compare codes between old and new members match (§6.7).
* `served_closed'`, `served_tight'`: every link of a served record is a digest the served view
  knows, and every served record is reachable from the served heads, when the same holds for the
  responder.
* `served_boundary'`: a served boundary digest is one the responder knows, and from it no `vis`
  record can be reached. The boundary hides nothing the requester may see.
* `agree_rel'`: take a view with the same heads as a relative store `(S, BS)`. Every digest
  reachable from its heads is a digest of `S` whose records in the view are all in `S`, or a
  digest only in `BS` that the view holds no record for. Or two records collide. Nothing is
  assumed about the view's own boundary.
* `newcomer_agree'`: so a view with the responder's heads, all of whose records are reachable
  from those heads, holds only the responder's records. Or two records collide.

With `BS = ∅` the responder is a closed store, and these say what the closed versions say
(`headsRel_empty`, `closedRel_empty_iff`).

**Four limits**, checked by `decide`: `after_record_served`, `phantom_boundary_indistinguishable`,
`below_boundary_not_vouched` and `Breaker2.relative_responder_not_closed`. The four limits of
links alone (`Chat.lean`) still hold.

This is the port of the scratch `docs/join-v2/Rel.lean` (review round 1) onto `Record` and
`Store`. One change: a record reaches another when the other's digest is reachable from its own
digest by `Reach` (`Defs.lean`), the reachability the rest of the spec uses (`mem_reachersOf`).
With that, `served_boundary'` speaks of digests, which is at least as strong as the scratch
statement about records.
-/

namespace Crdt.Merkle

namespace Toy

/-- A record written after seeing `r3` and `r4`: it joins the two branches. Hash `5`. -/
def r5 : R := ⟨5, {3, 4}, ()⟩

end Toy

/-! The joining chat, used for the examples. Alice holds the whole chat. Bob joined and was sent
`r2` only; `r4` was written after it. Later Carol joined and was sent `r5` only. -/

namespace Joining

/-- Alice's store, closed: `r0 ← r1 ← r2 ← r4`, and `r0 ← r3` (written at the same time as `r1`).
Its heads are `3` and `4`. -/
def alice : Store ℕ ℕ Unit := {Toy.r0, Toy.r1, Toy.r2, Toy.r3, Toy.r4}

/-- Bob's records after catch-up from Alice: `r2`, which he was sent, and `r4`, written after
it. -/
def bobF : Store ℕ ℕ Unit := {Toy.r2, Toy.r4}

/-- Bob's boundary after catch-up from Alice: `1`, which `r2` links, and `3`, Alice's other
head. -/
def bobB : Finset ℕ := {1, 3}

/-- Bob's records after Alice's `r5`, which joins `r3` and `r4`, arrives live. With the
boundary `bobB`, this is a relative store. -/
def bobS : Store ℕ ℕ Unit := {Toy.r2, Toy.r4, Toy.r5}

/-- Carol's records after catch-up from Bob: `r5`, which she was sent. -/
def carolF : Store ℕ ℕ Unit := {Toy.r5}

/-- Carol's boundary after catch-up from Bob: `3` and `4`, which `r5` links. -/
def carolB : Finset ℕ := {3, 4}

end Joining

section Rel

variable {α H K : Type*} [DecidableEq α] [DecidableEq H] [DecidableEq K]
variable (hash : Record α H K → H)

/-! ## Views -/

/-- The digests a view `(F, B)` knows: the digests of its records, and its boundary digests. -/
def inView (F : Store α H K) (B : Finset H) : Finset H := digests hash F ∪ B

example : inView Toy.hash Joining.bobF Joining.bobB = {1, 2, 3, 4} := by decide

theorem mem_inView {F : Store α H K} {B : Finset H} {d : H} :
    d ∈ inView hash F B ↔ (∃ r ∈ F, hash r = d) ∨ d ∈ B := by
  rw [inView, Finset.mem_union, mem_digests]

/-- The digests that the records of `s` link. -/
def linksOf (s : Store α H K) : Finset H := s.biUnion Record.links

example : linksOf Joining.bobF = {1, 2} := by decide

theorem mem_linksOf {s : Store α H K} {d : H} : d ∈ linksOf s ↔ ∃ r ∈ s, d ∈ r.links :=
  Finset.mem_biUnion

/-- A bigger store links more digests. -/
theorem linksOf_mono {s t : Store α H K} (h : s ⊆ t) : linksOf s ⊆ linksOf t :=
  Finset.biUnion_subset_biUnion_of_subset_left _ h

/-- The heads of a view `(F, B)`: the digests it knows that none of its records link. These are
what a newcomer compares with other members. -/
def headsRel (F : Store α H K) (B : Finset H) : Finset H :=
  (inView hash F B).filter fun d ↦ d ∉ linksOf F

-- Bob's view has Alice's heads: `3` from the boundary, `4` from a record.
example : headsRel Toy.hash Joining.bobF Joining.bobB = {3, 4} := by decide

theorem mem_headsRel {F : Store α H K} {B : Finset H} {d : H} :
    d ∈ headsRel hash F B ↔ d ∈ inView hash F B ∧ d ∉ linksOf F :=
  Finset.mem_filter

/-- With no boundary, the heads of a view are the heads of its store. -/
theorem headsRel_empty (s : Store α H K) : headsRel hash s ∅ = heads hash s := by
  ext d
  rw [mem_headsRel, mem_inView, mem_heads, mem_linksOf]
  constructor
  · rintro ⟨⟨r, hr, hd⟩ | hb, hn⟩
    · exact ⟨r, hr, hd, fun r' hr' hl ↦ hn ⟨r', hr', hl⟩⟩
    · exact absurd hb (Finset.notMem_empty d)
  · rintro ⟨r, hr, hd, hn⟩
    exact ⟨.inl ⟨r, hr, hd⟩, fun ⟨r', hr', hl⟩ ↦ hn r' hr' hl⟩

example : headsRel Toy.hash Joining.alice ∅ = heads Toy.hash Joining.alice :=
  headsRel_empty Toy.hash _

/-- A view `(F, B)` is **closed relative to its boundary**: every link of each of its records is a
digest the view knows. A newcomer's store keeps this: it accepts a record when each link is a
held record or a boundary digest (§6.2). -/
def ClosedRel (F : Store α H K) (B : Finset H) : Prop := ∀ r ∈ F, r.links ⊆ inView hash F B

instance (F : Store α H K) (B : Finset H) : Decidable (ClosedRel hash F B) := by
  unfold ClosedRel; infer_instance

example : ClosedRel Toy.hash Joining.bobF Joining.bobB := by decide
example : ClosedRel Toy.hash Joining.bobS Joining.bobB := by decide
-- Without the boundary digest `1`, the link of `r2` does not resolve.
example : ¬ ClosedRel Toy.hash Joining.bobF {3} := by decide

/-- With no boundary, closed relative to the boundary is closed. -/
theorem closedRel_empty_iff (s : Store α H K) : ClosedRel hash s ∅ ↔ Closed hash s := by
  constructor
  · intro h r hr d hd
    rcases (mem_inView hash).mp (h r hr hd) with h' | hb
    · exact h'
    · exact absurd hb (Finset.notMem_empty d)
  · intro h r hr d hd
    exact (mem_inView hash).mpr (.inl (h r hr d hd))

example : ClosedRel Toy.hash Joining.alice ∅ := (closedRel_empty_iff Toy.hash _).mpr (by decide)

/-! Reachability in a view is `Reach` through its records, from its heads:
`Reach hash F (headsRel hash F B) d`. A boundary digest is reached, and nothing past it. -/

example : Reach Toy.hash Joining.bobF (headsRel Toy.hash Joining.bobF Joining.bobB) 1 := by decide
-- Bob's view stops at the boundary: `0`, which `r1` links, is not reachable in it.
example : ¬ Reach Toy.hash Joining.bobF (headsRel Toy.hash Joining.bobF Joining.bobB) 0 := by
  decide
example : Tight Toy.hash Joining.bobF (headsRel Toy.hash Joining.bobF Joining.bobB) := by decide

/-- One step back along a link: if `s`, a record of `S`, links digest `d`, then whatever is
reachable from `d` is reachable from `s`'s digest. -/
theorem reach_of_link {S : Store α H K} {s : Record α H K} {d x : H} (hs : s ∈ S)
    (hl : d ∈ s.links) (h : Reach hash S {d} x) : Reach hash S {hash s} x :=
  h.lift hash subset_rfl fun d' hd' ↦ by
    rw [Finset.mem_singleton.mp hd']
    exact .link hs (.head (Finset.mem_singleton_self _)) hl

/-- Something reachable from one digest `d` is `d` itself, or `d` is the digest of a record of
`S` (the first step of the path). -/
theorem reach_singleton {S : Store α H K} {d x : H} (h : Reach hash S {d} x) :
    x = d ∨ ∃ r ∈ S, hash r = d := by
  induction h with
  | head h => exact .inl (Finset.mem_singleton.mp h)
  | @link r _ hr _ _ ih =>
    rcases ih with he | h
    · exact .inr ⟨r, hr, he⟩
    · exact .inr h

/-! ## The served view -/

/-- The records a responder with records `S` serves in full to a requester who may see the
records `vis`: the records of `S` from whose digest, following links through `S`, the digest of a
`vis` record of `S` is reachable. Each `vis` record is served (with content), and so is each record
written after one (as structure: the `after` entries of §5). -/
def servedF (S : Store α H K) (vis : Record α H K → Prop) [DecidablePred vis] : Store α H K :=
  S.filter fun r ↦ ∃ t ∈ S, vis t ∧ Reach hash S {hash r} (hash t)

-- Alice serves Bob `r2`, which he was sent, and `r4`, written after it.
example : servedF Toy.hash Joining.alice (· = Toy.r2) = Joining.bobF := by decide
-- Bob serves Carol `r5`.
example : servedF Toy.hash Joining.bobS (· = Toy.r5) = Joining.carolF := by decide

theorem mem_servedF {S : Store α H K} {vis : Record α H K → Prop} [DecidablePred vis]
    {r : Record α H K} :
    r ∈ servedF hash S vis ↔ r ∈ S ∧ ∃ t ∈ S, vis t ∧ Reach hash S {hash r} (hash t) :=
  Finset.mem_filter

/-- The served records are records of the responder. -/
theorem servedF_subset (S : Store α H K) (vis : Record α H K → Prop) [DecidablePred vis] :
    servedF hash S vis ⊆ S :=
  Finset.filter_subset _ _

/-- A record of `S` that links a served record is served. -/
theorem servedF_of_link {S : Store α H K} {vis : Record α H K → Prop} [DecidablePred vis]
    {r s : Record α H K} (hr : r ∈ servedF hash S vis) (hs : s ∈ S) (hl : hash r ∈ s.links) :
    s ∈ servedF hash S vis := by
  obtain ⟨-, t, ht, hv, hreach⟩ := (mem_servedF hash).mp hr
  exact (mem_servedF hash).mpr ⟨hs, t, ht, hv, reach_of_link hash hs hl hreach⟩

/-- The boundary digests a responder with view `(S, BS)` serves to a requester who may see the
records `vis`: the digests its view knows that no served record has, and that a served record
links, or that no record of `S` links (the responder's other heads). For a closed responder,
`BS = ∅`. -/
def servedB' (S : Store α H K) (vis : Record α H K → Prop) [DecidablePred vis] (BS : Finset H) :
    Finset H :=
  (inView hash S BS).filter fun d ↦
    d ∉ digests hash (servedF hash S vis) ∧
      (d ∈ linksOf (servedF hash S vis) ∨ d ∉ linksOf S)

-- Alice, closed, serves Bob `1` (below `r2`) and `3` (her other head) as boundary.
example : servedB' Toy.hash Joining.alice (· = Toy.r2) ∅ = Joining.bobB := by decide
-- Bob, relative, serves Carol `3` (from his own boundary) and `4` (a record he holds).
example : servedB' Toy.hash Joining.bobS (· = Toy.r5) Joining.bobB = Joining.carolB := by decide

theorem mem_servedB' {S : Store α H K} {vis : Record α H K → Prop} [DecidablePred vis]
    {BS : Finset H} {d : H} :
    d ∈ servedB' hash S vis BS ↔ d ∈ inView hash S BS ∧ d ∉ digests hash (servedF hash S vis) ∧
      (d ∈ linksOf (servedF hash S vis) ∨ d ∉ linksOf S) :=
  Finset.mem_filter

/-- **The served view has exactly the responder's heads**, for any `vis`, with or without a
boundary on the responder's side. No collision clause. -/
theorem served_heads' (S : Store α H K) (vis : Record α H K → Prop) [DecidablePred vis]
    (BS : Finset H) :
    headsRel hash (servedF hash S vis) (servedB' hash S vis BS) = headsRel hash S BS := by
  ext d
  rw [mem_headsRel, mem_headsRel]
  constructor
  · rintro ⟨hin, hnl⟩
    rcases (mem_inView hash).mp hin with ⟨r, hr, hd⟩ | hb
    · refine ⟨(mem_inView hash).mpr (.inl ⟨r, servedF_subset hash S vis hr, hd⟩), fun hl ↦ ?_⟩
      obtain ⟨s, hs, hsl⟩ := mem_linksOf.mp hl
      exact hnl (mem_linksOf.mpr ⟨s, servedF_of_link hash hr hs (hd ▸ hsl), hsl⟩)
    · obtain ⟨hv, -, hlk⟩ := (mem_servedB' hash).mp hb
      exact ⟨hv, fun hl ↦ hlk.elim hnl (absurd hl)⟩
  · rintro ⟨hin, hnl⟩
    refine ⟨?_, fun hl ↦ hnl (linksOf_mono (servedF_subset hash S vis) hl)⟩
    by_cases hd : d ∈ digests hash (servedF hash S vis)
    · exact (mem_inView hash).mpr (.inl ((mem_digests hash).mp hd))
    · exact (mem_inView hash).mpr (.inr ((mem_servedB' hash).mpr ⟨hin, hd, .inr hnl⟩))

-- Bob, served by Alice, has Alice's heads.
example : headsRel Toy.hash (servedF Toy.hash Joining.alice (· = Toy.r2))
      (servedB' Toy.hash Joining.alice (· = Toy.r2) ∅) = headsRel Toy.hash Joining.alice ∅ :=
  served_heads' Toy.hash _ _ _
-- Carol, served by Bob (a former newcomer), has Bob's heads.
example : headsRel Toy.hash (servedF Toy.hash Joining.bobS (· = Toy.r5))
      (servedB' Toy.hash Joining.bobS (· = Toy.r5) Joining.bobB) =
    headsRel Toy.hash Joining.bobS Joining.bobB :=
  served_heads' Toy.hash _ _ _
-- A view that hides Alice's other head `3` has other heads: the comparison shows it.
example : headsRel Toy.hash Joining.bobF {1} ≠ headsRel Toy.hash Joining.alice ∅ := by decide

/-- **The served view is closed relative to its boundary** when the responder's view is. -/
theorem served_closed' {S : Store α H K} {vis : Record α H K → Prop} [DecidablePred vis]
    {BS : Finset H} (hS : ClosedRel hash S BS) :
    ClosedRel hash (servedF hash S vis) (servedB' hash S vis BS) := by
  intro r hr d hl
  by_cases hd : d ∈ digests hash (servedF hash S vis)
  · exact (mem_inView hash).mpr (.inl ((mem_digests hash).mp hd))
  · exact (mem_inView hash).mpr (.inr ((mem_servedB' hash).mpr
      ⟨hS r (servedF_subset hash S vis hr) hl, hd, .inl (mem_linksOf.mpr ⟨r, hr, hl⟩)⟩))

example : ClosedRel Toy.hash (servedF Toy.hash Joining.bobS (· = Toy.r5))
    (servedB' Toy.hash Joining.bobS (· = Toy.r5) Joining.bobB) :=
  served_closed' Toy.hash (by decide)

/-- **The served view is tight**: every served record is reachable from the served heads through
served records, when every record of the responder is reachable from its own heads. -/
theorem served_tight' {S : Store α H K} {vis : Record α H K → Prop} [DecidablePred vis]
    {BS : Finset H} (htight : Tight hash S (headsRel hash S BS)) :
    Tight hash (servedF hash S vis)
      (headsRel hash (servedF hash S vis) (servedB' hash S vis BS)) := by
  have key : ∀ d, Reach hash S (headsRel hash S BS) d →
      ∀ r ∈ servedF hash S vis, hash r = d →
        Reach hash (servedF hash S vis)
          (headsRel hash (servedF hash S vis) (servedB' hash S vis BS)) d := by
    intro d hd
    induction hd with
    | head h =>
      intro _ _ _
      exact .head ((served_heads' hash S vis BS).symm ▸ h)
    | @link s d hs _ hl ih =>
      intro r hr hrd
      have hsF : s ∈ servedF hash S vis := servedF_of_link hash hr hs (hrd ▸ hl)
      exact .link hsF (ih s hsF rfl) hl
  intro r hr
  exact key _ (htight r (servedF_subset hash S vis hr)) r hr rfl

example : Tight Toy.hash (servedF Toy.hash Joining.bobS (· = Toy.r5))
    (headsRel Toy.hash (servedF Toy.hash Joining.bobS (· = Toy.r5))
      (servedB' Toy.hash Joining.bobS (· = Toy.r5) Joining.bobB)) :=
  served_tight' Toy.hash (by decide)

/-- **No hidden hole.** A served boundary digest is one the responder's view knows, and from it,
following links through the responder's records, no `vis` record is reachable. -/
theorem served_boundary' {S : Store α H K} {vis : Record α H K → Prop} [DecidablePred vis]
    {BS : Finset H} {d : H} (hb : d ∈ servedB' hash S vis BS) :
    d ∈ inView hash S BS ∧ ∀ t ∈ S, vis t → ¬ Reach hash S {d} (hash t) := by
  obtain ⟨hin, hnot, -⟩ := (mem_servedB' hash).mp hb
  refine ⟨hin, fun t ht hv hreach ↦ hnot ((mem_digests hash).mpr ?_)⟩
  rcases reach_singleton hash hreach with he | ⟨r, hr, hrd⟩
  · exact ⟨t, (mem_servedF hash).mpr ⟨ht, t, ht, hv, .head (Finset.mem_singleton_self _)⟩, he⟩
  · exact ⟨r, (mem_servedF hash).mpr ⟨hr, t, ht, hv, hrd ▸ hreach⟩, hrd⟩

-- Bob's boundary digest `1` is Alice's, and from it `r2`, which he was sent, is not reachable.
example : 1 ∈ inView Toy.hash Joining.alice ∅ ∧
    ∀ t ∈ Joining.alice, t = Toy.r2 → ¬ Reach Toy.hash Joining.alice {1} (Toy.hash t) :=
  served_boundary' Toy.hash (vis := (· = Toy.r2)) (by decide)

/-! ## Agreement relative to a boundary -/

/-- **Agreement relative to a boundary.** A view `(F, B)` has the same heads as a responder's
view `(S, BS)`, every link of a record of `S` is a digest `(S, BS)` knows, and the view holds a
record with a digest of `BS` only if `S` holds one with that digest too. Then each digest
reachable from the view's heads is a digest of `S`, and every record of the view with that digest
is in `S`; or it is a digest only of `BS`, and the view holds no record for it. Or two records of
`S ∪ F` collide. Nothing is assumed about `B`. -/
theorem agree_rel' {S F : Store α H K} {B BS : Finset H}
    (hS : ClosedRel hash S BS)
    (hh : headsRel hash F B = headsRel hash S BS)
    (hFB : ∀ r ∈ F, hash r ∈ BS → hash r ∈ digests hash S) :
    ∀ d, Reach hash F (headsRel hash F B) d →
      (d ∈ digests hash S ∧ ∀ r ∈ F, hash r = d → r ∈ S) ∨
        (d ∈ BS ∧ d ∉ digests hash S ∧ ∀ r ∈ F, hash r ≠ d) ∨
        CollisionIn hash (S ∪ F) := by
  -- A digest that the responder's view knows meets the conclusion.
  have fromView : ∀ d ∈ inView hash S BS,
      (d ∈ digests hash S ∧ ∀ r ∈ F, hash r = d → r ∈ S) ∨
        (d ∈ BS ∧ d ∉ digests hash S ∧ ∀ r ∈ F, hash r ≠ d) ∨
        CollisionIn hash (S ∪ F) := by
    intro d hin
    by_cases hs : d ∈ digests hash S
    · obtain ⟨r', hr', hd⟩ := (mem_digests hash).mp hs
      by_cases hall : ∀ r ∈ F, hash r = d → r ∈ S
      · exact .inl ⟨hs, hall⟩
      · obtain ⟨r, hr, hrd, hrS⟩ : ∃ r ∈ F, hash r = d ∧ r ∉ S := by
          by_contra hno
          exact hall fun r hr hrd ↦ by_contra fun hrS ↦ hno ⟨r, hr, hrd, hrS⟩
        exact .inr (.inr (CollisionIn.of_mem hash (Finset.mem_union_left F hr')
          (Finset.mem_union_right S hr) (fun e ↦ hrS (e ▸ hr')) (hd.trans hrd.symm)))
    · rcases (mem_inView hash).mp hin with h | hb
      · exact absurd ((mem_digests hash).mpr h) hs
      · exact .inr (.inl ⟨hb, hs, fun r hr hrd ↦ hs (hrd ▸ hFB r hr (hrd ▸ hb))⟩)
  intro d hd
  induction hd with
  | head h =>
    have h' : _ ∈ headsRel hash S BS := hh ▸ h
    exact fromView _ ((mem_headsRel hash).mp h').1
  | @link r d hr _ hl ih =>
    rcases ih with ⟨-, hall⟩ | ⟨-, -, hne⟩ | hc
    · exact fromView d (hS r (hall r hr rfl) hl)
    · exact absurd rfl (hne r hr)
    · exact .inr (.inr hc)

-- Carol's view against Bob's relative store: digest `3` is only in Bob's boundary, and Carol
-- holds no record for it.
example : (3 ∈ digests Toy.hash Joining.bobS ∧
      ∀ r ∈ Joining.carolF, Toy.hash r = 3 → r ∈ Joining.bobS) ∨
    (3 ∈ Joining.bobB ∧ 3 ∉ digests Toy.hash Joining.bobS ∧
      ∀ r ∈ Joining.carolF, Toy.hash r ≠ 3) ∨
    CollisionIn Toy.hash (Joining.bobS ∪ Joining.carolF) :=
  agree_rel' Toy.hash (B := Joining.carolB) (by decide) (by decide) (by decide) 3 (by decide)

/-- **End to end.** A view with the same heads as a responder's view `(S, BS)`, all of whose
records are reachable from those heads, and which holds a record with a digest of `BS` only if `S`
holds one with that digest too, holds only records of `S`. Or two records of `S ∪ F` collide. The
served view meets every hypothesis (`served_heads'`, `served_tight'`, `servedF_subset`). -/
theorem newcomer_agree' {S F : Store α H K} {B BS : Finset H} (hS : ClosedRel hash S BS)
    (hh : headsRel hash F B = headsRel hash S BS)
    (hFB : ∀ r ∈ F, hash r ∈ BS → hash r ∈ digests hash S)
    (htF : Tight hash F (headsRel hash F B)) :
    F ⊆ S ∨ CollisionIn hash (S ∪ F) := by
  by_cases hc : CollisionIn hash (S ∪ F)
  · exact .inr hc
  · refine .inl fun r hr ↦ ?_
    rcases agree_rel' hash hS hh hFB _ (htF r hr) with ⟨-, hall⟩ | ⟨-, -, hne⟩ | h
    · exact hall r hr rfl
    · exact absurd rfl (hne r hr)
    · exact absurd h hc

-- Carol's view, against Bob's relative store.
example : Joining.carolF ⊆ Joining.bobS ∨
    CollisionIn Toy.hash (Joining.bobS ∪ Joining.carolF) :=
  newcomer_agree' Toy.hash (B := Joining.carolB) (BS := Joining.bobB)
    (by decide) (by decide) (by decide) (by decide)
-- Bob's view, against Alice's closed store.
example : Joining.bobF ⊆ Joining.alice ∨ CollisionIn Toy.hash (Joining.alice ∪ Joining.bobF) :=
  newcomer_agree' Toy.hash (B := Joining.bobB) (BS := ∅)
    (by decide) (by decide) (by decide) (by decide)
-- A view with Bob's heads that holds a fake `r4` (same digest `4`, other links): the theorem
-- names the collision.
example : CollisionIn Toy.hash (Joining.alice ∪ {Toy.r2, (⟨4, {1}, ()⟩ : Toy.R)}) := by decide

/-! ## What a relative store cannot do

Four concrete cases, checked by `decide`. -/

/-- **Limit 1: a record written after one sent to the newcomer reaches him as structure.** Bob
was sent `r2` only, but Alice serves him `r4` (its author and links) because it links `r2`. Serving
`4` as a bare boundary digest instead would leave `2` a head of his view, so his heads would differ
from Alice's (§6.4: metadata, never content). -/
theorem after_record_served :
    Toy.r4 ∈ servedF Toy.hash Joining.alice (· = Toy.r2) ∧ Toy.r4 ≠ Toy.r2 ∧
      headsRel Toy.hash {Toy.r2} {1, 3, 4} ≠ headsRel Toy.hash Joining.alice ∅ := by
  decide

/-- **Limit 2: a boundary digest cannot be checked.** In world 1, Alice's closed store holds
`r7`, a record Bob was not sent, and she serves its digest `7` as a head. In world 2, Mallory's
relative store has a boundary digest `7` that no record has: she made it up. Bob, sent `r2`, gets
the same view from both. A newcomer has no preimage to check a digest against; the responder is
named as its voucher (§6.2), and a relative store's own records never link a boundary digest. -/
theorem phantom_boundary_indistinguishable :
    let alice : Store ℕ ℕ Unit := {Toy.r0, Toy.r1, Toy.r2, Toy.r7}
    let mallory : Store ℕ ℕ Unit := {Toy.r2}
    -- World 1: Alice's store is closed, and `7` is the digest of a record she holds.
    (ClosedRel Toy.hash alice ∅ ∧ 7 ∈ digests Toy.hash alice) ∧
      -- World 2: Mallory's view is closed relative to its boundary, and no record has digest `7`.
      (ClosedRel Toy.hash mallory {1, 7} ∧ 7 ∉ digests Toy.hash mallory) ∧
      -- Bob receives the same records and the same boundary.
      servedF Toy.hash alice (· = Toy.r2) = servedF Toy.hash mallory (· = Toy.r2) ∧
      servedB' Toy.hash alice (· = Toy.r2) ∅ = servedB' Toy.hash mallory (· = Toy.r2) {1, 7} := by
  decide

/-- **Limit 3: agreement with a relative store says nothing below its boundary.** Bob's store is
`r2` above the boundary digest `1`. A view that also holds `r1`, with boundary `0`, has Bob's heads,
is closed relative to its boundary, and every record of it is reachable from its heads. Yet it
holds a record Bob does not hold, and no two records collide. This is why `agree_rel'` and
`newcomer_agree'` assume the view holds no record for a digest only in the responder's boundary. -/
theorem below_boundary_not_vouched :
    let bob : Store ℕ ℕ Unit := {Toy.r2}
    let view : Store ℕ ℕ Unit := {Toy.r1, Toy.r2}
    ClosedRel Toy.hash bob {1} ∧ ClosedRel Toy.hash view {0} ∧
      headsRel Toy.hash view {0} = headsRel Toy.hash bob {1} ∧
      Tight Toy.hash view (headsRel Toy.hash view {0}) ∧
      ¬ (view ⊆ bob ∨ CollisionIn Toy.hash (bob ∪ view)) := by
  decide

/-! Found by breaker 2 of review round 1: before round 1, a responder served only digests of its
own records as boundary, which is `servedB'` with `BS = ∅`. -/

namespace Breaker2

/-- **Limit 4: a relative responder that ignores its own boundary serves a view that is not
closed.** Bob holds `r2`, which links `1`, a digest only in his boundary. Serving Carol `r2` with
the boundary of a closed store leaves the link `1` unresolved, so she cannot accept `r2`. -/
theorem relative_responder_not_closed :
    ¬ ClosedRel Toy.hash (servedF Toy.hash {Toy.r2} (· = Toy.r2))
      (servedB' Toy.hash {Toy.r2} (· = Toy.r2) ∅) := by
  decide

/-- With Bob's boundary `{1}` served too, the same view is closed (`served_closed'`). -/
theorem relative_responder_closed' :
    ClosedRel Toy.hash (servedF Toy.hash {Toy.r2} (· = Toy.r2))
      (servedB' Toy.hash {Toy.r2} (· = Toy.r2) {1}) :=
  served_closed' Toy.hash (by decide)

end Breaker2

end Rel

end Crdt.Merkle
