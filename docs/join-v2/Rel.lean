-- Reference copy from the JOIN_PLAN v2 review, extended after review round 1 (2026-11-01). Not
-- built by any lake target. Imports nothing; checked with `lake env lean` (Lean v4.35.0). No sorry.
/-!
# Relative views: a newcomer's store with an opaque boundary (scratch, Mathlib-free)

`R` records, `H` digests, `hash`, `links`. A store is a predicate on records. A *view* is
`(F, B)`: full records `F` and boundary digests `B` (leaves: their links are unknown).

* `agree_rel`: if a view and a closed store have the same heads, every full record of the view
  reachable from the heads is in the store, and every reachable digest is a store digest, or two
  records share a digest. Needs NOTHING about `B`.
* `served_heads`, `served_closed`, `served_tight`: the view a responder serves for predicate
  `vis` (F = records reaching a `vis` record; B = digests of non-F records linked by F, or heads)
  has exactly the responder's heads, is closed relative to B, and is tight.
* Round 1: a responder whose own store is relative, `(S, BS)` (a former newcomer, e.g. the adder
  of the next newcomer). `Breaker2.relative_responder_not_closed`: serving only stored records
  gives a view the next newcomer cannot accept. The primed theorems serve `BS` digests too
  (`ServedB'`) and generalise every statement above; with `BS = noB` they say what the unprimed
  ones say.
-/

namespace Rel

variable {R H : Type} (hash : R → H) (links : R → List H)

def Collision (S : R → Prop) : Prop := ∃ x y, S x ∧ S y ∧ x ≠ y ∧ hash x = hash y

def Closed (S : R → Prop) : Prop := ∀ r, S r → ∀ d ∈ links r, ∃ r', S r' ∧ hash r' = d

def InView (F : R → Prop) (B : H → Prop) (d : H) : Prop := (∃ r, F r ∧ hash r = d) ∨ B d

def Linked (F : R → Prop) (d : H) : Prop := ∃ r, F r ∧ d ∈ links r

/-- Heads of a view: in it, linked by none of its full records. A store is the view `(S, ⊥)`. -/
def HeadV (F : R → Prop) (B : H → Prop) (d : H) : Prop :=
  InView hash F B d ∧ ¬ Linked links F d

def ClosedRel (F : R → Prop) (B : H → Prop) : Prop :=
  ∀ r, F r → ∀ d ∈ links r, InView hash F B d

/-- Digests reachable from `hs` by following links of full records of `F`. -/
inductive ReachV (F : R → Prop) (hs : H → Prop) : H → Prop
  | head {d : H} : hs d → ReachV F hs d
  | step {r : R} {d : H} : ReachV F hs (hash r) → F r → d ∈ links r → ReachV F hs d

def noB : H → Prop := fun _ => False

/-- **Agreement relative to a boundary.** -/
theorem agree_rel {S F : R → Prop} {B : H → Prop}
    (hS : Closed hash links S)
    (hh : ∀ d, HeadV hash links F B d ↔ HeadV hash links S noB d) :
    ∀ d, ReachV hash links F (HeadV hash links F B) d →
      Collision hash (fun x => S x ∨ F x) ∨
        ((∃ r', S r' ∧ hash r' = d) ∧ ∀ r, F r → hash r = d → S r) := by
  -- From a store record `r'` with digest `d`: either every full record with digest `d` is in
  -- the store, or there is a collision.
  have finish : ∀ d r', S r' → hash r' = d →
      Collision hash (fun x => S x ∨ F x) ∨
        ((∃ r', S r' ∧ hash r' = d) ∧ ∀ r, F r → hash r = d → S r) := by
    intro d r' hr' hd
    by_cases hall : ∀ r, F r → hash r = d → S r
    · exact .inr ⟨⟨r', hr', hd⟩, hall⟩
    · apply Or.inl
      apply Classical.byContradiction
      intro hno
      apply hall
      intro r hr hrd
      apply Classical.byContradiction
      intro hnS
      exact hno ⟨r', r, .inl hr', .inr hr, fun h => hnS (h ▸ hr'), hd.trans hrd.symm⟩
  intro d hd
  induction hd with
  | head h =>
    obtain ⟨hin, -⟩ := (hh _).1 h
    rcases hin with ⟨r', hr', hd⟩ | hb
    · exact finish _ r' hr' hd
    · exact hb.elim
  | @step r d _ hr hl ih =>
    rcases ih with hc | ⟨-, hall⟩
    · exact .inl hc
    · obtain ⟨r'', hr'', hd⟩ := hS r (hall r hr rfl) d hl
      exact finish d r'' hr'' hd

/-! ## The served view -/

/-- `r` reaches `t` by following links to records of `S` (reflexive). -/
inductive Reaches (S : R → Prop) : R → R → Prop
  | refl (r : R) : Reaches S r r
  | step {r m t : R} : hash m ∈ links r → S m → Reaches S m t → Reaches S r t

/-- Full records served to the requester: store records reaching a `vis` record. -/
def ServedF (S vis : R → Prop) (r : R) : Prop :=
  S r ∧ ∃ t, S t ∧ vis t ∧ Reaches hash links S r t

/-- Boundary digests served: digests of store records outside `ServedF`, linked by a served
record or not linked at all (heads). -/
def ServedB (S vis : R → Prop) (d : H) : Prop :=
  (∃ r, S r ∧ hash r = d ∧ ¬ ServedF hash links S vis r) ∧
    (Linked links (ServedF hash links S vis) d ∨ ¬ Linked links S d)

/-- **The served view has exactly the responder's heads.** No hypothesis on collisions. -/
theorem served_heads {S vis : R → Prop} :
    ∀ d, HeadV hash links (ServedF hash links S vis) (ServedB hash links S vis) d ↔
      HeadV hash links S noB d := by
  intro d
  constructor
  · rintro ⟨hin, hnl⟩
    refine ⟨?_, ?_⟩
    · rcases hin with ⟨r, ⟨hS, -⟩, hd⟩ | ⟨⟨r, hS, hd, -⟩, -⟩
      · exact .inl ⟨r, hS, hd⟩
      · exact .inl ⟨r, hS, hd⟩
    · rintro ⟨s, hs, hl⟩
      rcases hin with ⟨r, ⟨hrS, t, htS, hvis, hreach⟩, hd⟩ | ⟨-, hlinked | hnot⟩
      · apply hnl
        refine ⟨s, ⟨hs, t, htS, hvis, ?_⟩, hl⟩
        exact .step (hd ▸ hl) hrS hreach
      · exact hnl hlinked
      · exact hnot ⟨s, hs, hl⟩
  · rintro ⟨hin, hnl⟩
    refine ⟨?_, ?_⟩
    · rcases hin with ⟨r, hS, hd⟩ | hb
      · by_cases hF : ServedF hash links S vis r
        · exact .inl ⟨r, hF, hd⟩
        · exact .inr ⟨⟨r, hS, hd, hF⟩, .inr hnl⟩
      · exact hb.elim
    · rintro ⟨r, ⟨hS, -⟩, hl⟩
      exact hnl ⟨r, hS, hl⟩

/-- **The served view is closed relative to its boundary.** -/
theorem served_closed {S vis : R → Prop} (hS : Closed hash links S) :
    ClosedRel hash links (ServedF hash links S vis) (ServedB hash links S vis) := by
  intro r hF d hl
  obtain ⟨r', hr', hd⟩ := hS r hF.1 d hl
  by_cases hF' : ServedF hash links S vis r'
  · exact .inl ⟨r', hF', hd⟩
  · exact .inr ⟨⟨r', hr', hd, hF'⟩, .inl ⟨r, hF, hl⟩⟩

/-- **The served view is tight** when the store is: every served record is reachable from the
view's heads through served records. -/
theorem served_tight {S vis : R → Prop}
    (htight : ∀ r, S r → ReachV hash links S (HeadV hash links S noB) (hash r)) :
    ∀ r, ServedF hash links S vis r →
      ReachV hash links (ServedF hash links S vis)
        (HeadV hash links (ServedF hash links S vis) (ServedB hash links S vis)) (hash r) := by
  have key : ∀ d, ReachV hash links S (HeadV hash links S noB) d →
      ∀ r, ServedF hash links S vis r → hash r = d →
      ReachV hash links (ServedF hash links S vis)
        (HeadV hash links (ServedF hash links S vis) (ServedB hash links S vis)) d := by
    intro d hd
    induction hd with
    | head h =>
      intro _ _ _
      exact .head ((served_heads hash links _).2 h)
    | @step s d _ hs hl ih =>
      intro r hF hrd
      obtain ⟨hrS, t, htS, hvis, hreach⟩ := hF
      have hsF : ServedF hash links S vis s :=
        ⟨hs, t, htS, hvis, .step (hrd ▸ hl) hrS hreach⟩
      exact .step (ih s hsF rfl) hsF hl
  intro r hF
  exact key _ (htight r hF.1) r hF rfl

/-- **No hidden hole.** A boundary digest is the digest of a record that reaches no `vis`
record, unless two records share it. -/
theorem served_boundary {S vis : R → Prop} {d : H} (hb : ServedB hash links S vis d) :
    ∃ r, S r ∧ hash r = d ∧ ∀ t, S t → vis t → ¬ Reaches hash links S r t := by
  obtain ⟨⟨r, hS, hd, hF⟩, -⟩ := hb
  exact ⟨r, hS, hd, fun t ht hv hreach => hF ⟨hS, t, ht, hv, hreach⟩⟩

/-- End to end: a newcomer whose view has the served heads agrees with the responder's store. -/
theorem newcomer_agree {S F : R → Prop} {B : H → Prop} (hS : Closed hash links S)
    (hh : ∀ d, HeadV hash links F B d ↔ HeadV hash links S noB d)
    (htF : ∀ r, F r → ReachV hash links F (HeadV hash links F B) (hash r)) :
    Collision hash (fun x => S x ∨ F x) ∨ ∀ r, F r → S r := by
  by_cases hc : Collision hash (fun x => S x ∨ F x)
  · exact .inl hc
  · refine .inr fun r hr => ?_
    rcases agree_rel hash links hS hh _ (htF r hr) with h | ⟨-, hall⟩
    · exact absurd h hc
    · exact hall r hr rfl

/-! ## Round 1: a responder whose own store is relative

Found by breaker 2 of review round 1 (counterexample and `served_closed'`, `served_heads'`). -/

/-- Boundary digests served by a responder with its own boundary `BS`: digests in its view that no
served record has, linked by a served record or not linked at all (heads). -/
def ServedB' (S vis : R → Prop) (BS : H → Prop) (d : H) : Prop :=
  (InView hash S BS d ∧ ¬ ∃ r, ServedF hash links S vis r ∧ hash r = d) ∧
    (Linked links (ServedF hash links S vis) d ∨ ¬ Linked links S d)

/-- **The served view is closed relative to its boundary**, for a relative responder. -/
theorem served_closed' {S vis : R → Prop} {BS : H → Prop} (hS : ClosedRel hash links S BS) :
    ClosedRel hash links (ServedF hash links S vis) (ServedB' hash links S vis BS) := by
  intro r hF d hl
  by_cases hd : ∃ r', ServedF hash links S vis r' ∧ hash r' = d
  · exact .inl hd
  · exact .inr ⟨⟨hS r hF.1 d hl, hd⟩, .inl ⟨r, hF, hl⟩⟩

/-- **The served view has exactly the responder's heads**, for a relative responder. -/
theorem served_heads' {S vis : R → Prop} {BS : H → Prop} :
    ∀ d, HeadV hash links (ServedF hash links S vis) (ServedB' hash links S vis BS) d ↔
      HeadV hash links S BS d := by
  intro d
  constructor
  · rintro ⟨hin, hnl⟩
    refine ⟨?_, ?_⟩
    · rcases hin with ⟨r, ⟨hS, -⟩, hd⟩ | ⟨⟨hv, -⟩, -⟩
      · exact .inl ⟨r, hS, hd⟩
      · exact hv
    · rintro ⟨s, hs, hl⟩
      rcases hin with ⟨r, ⟨hrS, t, htS, hvis, hreach⟩, hd⟩ | ⟨-, hlinked | hnot⟩
      · exact hnl ⟨s, ⟨hs, t, htS, hvis, .step (hd ▸ hl) hrS hreach⟩, hl⟩
      · exact hnl hlinked
      · exact hnot ⟨s, hs, hl⟩
  · rintro ⟨hin, hnl⟩
    refine ⟨?_, ?_⟩
    · by_cases hF : ∃ r, ServedF hash links S vis r ∧ hash r = d
      · exact .inl hF
      · exact .inr ⟨⟨hin, hF⟩, .inr hnl⟩
    · rintro ⟨r, ⟨hS, -⟩, hl⟩
      exact hnl ⟨r, hS, hl⟩

/-- **The served view is tight** when the relative store is. -/
theorem served_tight' {S vis : R → Prop} {BS : H → Prop}
    (htight : ∀ r, S r → ReachV hash links S (HeadV hash links S BS) (hash r)) :
    ∀ r, ServedF hash links S vis r →
      ReachV hash links (ServedF hash links S vis)
        (HeadV hash links (ServedF hash links S vis) (ServedB' hash links S vis BS)) (hash r) := by
  have key : ∀ d, ReachV hash links S (HeadV hash links S BS) d →
      ∀ r, ServedF hash links S vis r → hash r = d →
      ReachV hash links (ServedF hash links S vis)
        (HeadV hash links (ServedF hash links S vis) (ServedB' hash links S vis BS)) d := by
    intro d hd
    induction hd with
    | head h =>
      intro _ _ _
      exact .head ((served_heads' hash links _).2 h)
    | @step s d _ hs hl ih =>
      intro r hF hrd
      obtain ⟨hrS, t, htS, hvis, hreach⟩ := hF
      have hsF : ServedF hash links S vis s :=
        ⟨hs, t, htS, hvis, .step (hrd ▸ hl) hrS hreach⟩
      exact .step (ih s hsF rfl) hsF hl
  intro r hF
  exact key _ (htight r hF.1) r hF rfl

/-- **No hidden hole**, for a relative responder: a served boundary digest is in the responder's
view, and every responder record with that digest reaches no `vis` record. -/
theorem served_boundary' {S vis : R → Prop} {BS : H → Prop} {d : H}
    (hb : ServedB' hash links S vis BS d) :
    InView hash S BS d ∧ ∀ r, S r → hash r = d → ∀ t, S t → vis t → ¬ Reaches hash links S r t := by
  obtain ⟨⟨hin, hF⟩, -⟩ := hb
  exact ⟨hin, fun r hS hd t ht hv hreach => hF ⟨r, ⟨hS, t, ht, hv, hreach⟩, hd⟩⟩

/-- **Agreement relative to a boundary, against a relative store** `(S, BS)` closed relative to
`BS`. Every digest reachable from the view's heads is a store digest whose full records in the
view are all in the store, or a digest only in `BS` that the view holds no record for, or two
records collide. `hFB`: below the responder's boundary the view knows nothing the responder does
not (true of every served view, whose records are the responder's). With `BS = noB` this is
`agree_rel`. -/
theorem agree_rel' {S F : R → Prop} {B BS : H → Prop}
    (hS : ClosedRel hash links S BS)
    (hh : ∀ d, HeadV hash links F B d ↔ HeadV hash links S BS d)
    (hFB : ∀ r, F r → BS (hash r) → ∃ r', S r' ∧ hash r' = hash r) :
    ∀ d, ReachV hash links F (HeadV hash links F B) d →
      Collision hash (fun x => S x ∨ F x) ∨
        ((∃ r', S r' ∧ hash r' = d) ∧ ∀ r, F r → hash r = d → S r) ∨
        (BS d ∧ (¬ ∃ r', S r' ∧ hash r' = d) ∧ ∀ r, F r → hash r ≠ d) := by
  have finish : ∀ d r', S r' → hash r' = d →
      Collision hash (fun x => S x ∨ F x) ∨
        ((∃ r', S r' ∧ hash r' = d) ∧ ∀ r, F r → hash r = d → S r) := by
    intro d r' hr' hd
    by_cases hall : ∀ r, F r → hash r = d → S r
    · exact .inr ⟨⟨r', hr', hd⟩, hall⟩
    · apply Or.inl
      apply Classical.byContradiction
      intro hno
      apply hall
      intro r hr hrd
      apply Classical.byContradiction
      intro hnS
      exact hno ⟨r', r, .inl hr', .inr hr, fun h => hnS (h ▸ hr'), hd.trans hrd.symm⟩
  have fromView : ∀ d, InView hash S BS d →
      Collision hash (fun x => S x ∨ F x) ∨
        ((∃ r', S r' ∧ hash r' = d) ∧ ∀ r, F r → hash r = d → S r) ∨
        (BS d ∧ (¬ ∃ r', S r' ∧ hash r' = d) ∧ ∀ r, F r → hash r ≠ d) := by
    intro d hin
    by_cases hs : ∃ r', S r' ∧ hash r' = d
    · obtain ⟨r', hr', hd⟩ := hs
      rcases finish d r' hr' hd with h | h
      · exact .inl h
      · exact .inr (.inl h)
    · rcases hin with h | hb
      · exact absurd h hs
      · refine .inr (.inr ⟨hb, hs, fun r hr hrd => ?_⟩)
        obtain ⟨r', hr', hd⟩ := hFB r hr (hrd ▸ hb)
        exact hs ⟨r', hr', hd.trans hrd⟩
  intro d hd
  induction hd with
  | head h => exact fromView _ ((hh _).1 h).1
  | @step r d _ hr hl ih =>
    rcases ih with hc | ⟨-, hall⟩ | ⟨-, -, hne⟩
    · exact .inl hc
    · exact fromView d (hS r (hall r hr rfl) d hl)
    · exact absurd rfl (hne r hr)

/-- End to end, for a relative responder: a tight view with the responder's heads that knows
nothing below the responder's boundary holds only records of the responder's store, or two
records collide. The served view satisfies every hypothesis (`served_heads'`, `served_tight'`,
and its records are the responder's). -/
theorem newcomer_agree' {S F : R → Prop} {B BS : H → Prop} (hS : ClosedRel hash links S BS)
    (hh : ∀ d, HeadV hash links F B d ↔ HeadV hash links S BS d)
    (hFB : ∀ r, F r → BS (hash r) → ∃ r', S r' ∧ hash r' = hash r)
    (htF : ∀ r, F r → ReachV hash links F (HeadV hash links F B) (hash r)) :
    Collision hash (fun x => S x ∨ F x) ∨ ∀ r, F r → S r := by
  by_cases hc : Collision hash (fun x => S x ∨ F x)
  · exact .inl hc
  · refine .inr fun r hr => ?_
    rcases agree_rel' hash links hS hh hFB _ (htF r hr) with h | ⟨-, hall⟩ | ⟨-, -, hne⟩
    · exact absurd h hc
    · exact hall r hr rfl
    · exact absurd rfl (hne r hr)

end Rel

/-! Breaker 2's counterexample: before round 1, a relative responder's served view was not
closed. Records are Nats, hash = id. Record 2 links digest 1; digest 1 is only in the
responder's own boundary, so `S = {2}` is not `Closed`, and the old `ServedB` (stored records
only) leaves 1 out. -/
namespace Breaker2
open Rel
def lk : Nat → List Nat := fun r => if r = 2 then [1] else []
def S : Nat → Prop := fun r => r = 2
def vis : Nat → Prop := fun r => r = 2

theorem relative_responder_not_closed :
    ¬ ClosedRel id lk (ServedF id lk S vis) (ServedB id lk S vis) := by
  intro h
  have hF : ServedF id lk S vis 2 := ⟨rfl, 2, rfl, rfl, .refl 2⟩
  have h1 : (1 : Nat) ∈ lk 2 := by simp [lk]
  rcases h 2 hF 1 h1 with ⟨r, ⟨hS, -⟩, hr⟩ | ⟨⟨r, hS, hr, -⟩, -⟩
  · simp [S] at hS; subst hS; simp at hr
  · simp [S] at hS; subst hS; simp at hr

/-- With the responder's boundary `{1}` served, the same view is closed. -/
theorem relative_responder_closed' :
    ClosedRel id lk (ServedF id lk S vis) (ServedB' id lk S vis (· = 1)) :=
  served_closed' id lk (fun r hr d hd => by
    simp [S] at hr; subst hr; simp [lk] at hd; exact .inr hd)
end Breaker2

#print axioms Rel.agree_rel
#print axioms Rel.served_heads
#print axioms Rel.served_closed
#print axioms Rel.served_tight
#print axioms Rel.served_boundary
#print axioms Rel.newcomer_agree
#print axioms Rel.served_closed'
#print axioms Rel.served_heads'
#print axioms Rel.served_tight'
#print axioms Rel.served_boundary'
#print axioms Rel.agree_rel'
#print axioms Rel.newcomer_agree'
#print axioms Breaker2.relative_responder_not_closed
#print axioms Breaker2.relative_responder_closed'
