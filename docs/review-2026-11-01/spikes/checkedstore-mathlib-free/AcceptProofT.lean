import Zrdt.CoreT
import Zrdt.Core
/-! Option 1 scratch: prove `accept` preserves the Mathlib-free `Built`, core/Std only. -/
namespace ZrdtT

theorem Ordered.links {l : List Rec} (h : Ordered l) :
    ∀ r ∈ l, ∀ d ∈ r.links, ∃ r' ∈ l, hashRecord r' = d := by
  induction h with
  | nil => simp
  | cons hr _ ih =>
    intro x hx d hd
    rcases List.mem_cons.mp hx with rfl | hx
    · obtain ⟨r', hr', he⟩ := hr d hd
      exact ⟨r', List.mem_cons_of_mem _ hr', he⟩
    · obtain ⟨r', hr', he⟩ := ih x hx d hd
      exact ⟨r', List.mem_cons_of_mem _ hr', he⟩

/-- Closure follows from the certificate. -/
theorem Built.closed {c : RawStore} (h : Built c) :
    ∀ (k : Digest) (r : Rec), c.map[k]? = some r → ∀ d ∈ r.links, d ∈ c.map := by
  intro k r hk d hd
  obtain ⟨l, hl, hmem⟩ := h.order
  obtain ⟨r', hr', he⟩ := hl.links r ((hmem r).mpr ⟨k, hk⟩) d hd
  obtain ⟨k', hk'⟩ := (hmem r').mp hr'
  have := h.keys k' r' hk'
  subst he; subst this
  exact Std.ExtTreeMap.mem_iff_isSome_getElem?.mpr (by simp [hk'])

theorem rawAccept_built {c : RawStore} (h : Built c) (r : Rec) : Built (rawAccept c r).2 := by
  unfold rawAccept
  by_cases hg : r.payload.group ≠ c.group
  · simpa [hg] using h
  simp only [hg, ite_false]
  split
  · split <;> exact h
  · rename_i hnone
    split
    · rename_i hmiss
      have hres : ∀ x ∈ r.links, x ∈ c.map := by
        intro x hx
        have := List.isEmpty_iff.mp hmiss
        rw [List.filter_eq_nil_iff] at this
        have := this x (by simpa using hx)
        exact Std.ExtTreeMap.mem_iff_contains.mpr (by simpa using this)
      have hcl := h.closed
      have hdnot : hashRecord r ∉ c.map := by
        simp [Std.ExtTreeMap.mem_iff_isSome_getElem?, hnone]
      simp only at *
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro k x hk
        rw [Std.ExtTreeMap.getElem?_insert] at hk
        split at hk
        · rename_i he; cases hk; simpa using he
        · exact h.keys k x hk
      · intro k x hk
        rw [Std.ExtTreeMap.getElem?_insert] at hk
        split at hk
        · cases hk; simpa using hg
        · exact h.chat k x hk
      · intro d
        simp only [Std.ExtTreeSet.mem_insert, Std.ExtTreeSet.mem_filter, Std.ExtTreeMap.mem_insert,
          Std.ExtTreeMap.getElem?_insert, Std.LawfulEqCmp.compare_eq_iff_eq]
        constructor
        · rintro (rfl | ⟨hd, hnl⟩)
          · refine ⟨Or.inl rfl, fun k x hk => ?_⟩
            split at hk
            · cases hk; exact fun hl => hdnot (hres _ hl)
            · exact fun hl => hdnot (hcl k x hk _ hl)
          · have := (h.heads d).mp hd
            refine ⟨Or.inr this.1, fun k x hk => ?_⟩
            split at hk
            · cases hk; simpa using hnl
            · exact this.2 k x hk
        · rintro ⟨hd, hun⟩
          by_cases hdr : hashRecord r = d
          · exact Or.inl hdr
          right
          rcases hd with hd | hd
          · exact absurd hd hdr
          refine ⟨(h.heads d).mpr ⟨hd, fun k x hk => ?_⟩, ?_⟩
          · have hk' : hashRecord r ≠ k := by
              rintro rfl; simp [hnone] at hk
            have := hun k x (by simp [hk', hk])
            exact this
          · have := hun (hashRecord r) r (by simp)
            simpa using this
      · obtain ⟨l, hl, hmem⟩ := h.order
        refine ⟨r :: l, .cons (fun d hd => ?_) hl, fun x => ?_⟩
        · have hdm := hres d hd
          obtain ⟨x, hx⟩ : ∃ x, c.map[d]? = some x :=
            Option.isSome_iff_exists.mp (Std.ExtTreeMap.mem_iff_isSome_getElem?.mp hdm)
          exact ⟨x, (hmem x).mpr ⟨d, hx⟩, h.keys d x hx⟩
        · simp only [List.mem_cons, hmem, Std.ExtTreeMap.getElem?_insert]
          constructor
          · rintro (rfl | ⟨k, hk⟩)
            · exact ⟨hashRecord x, by simp⟩
            · refine ⟨k, ?_⟩
              have hk' : hashRecord r ≠ k := by rintro rfl; simp [hnone] at hk
              simp [hk', hk]
          · rintro ⟨k, hk⟩
            split at hk
            · cases hk; exact Or.inl rfl
            · exact Or.inr ⟨k, hk⟩
    · exact h

def CheckedStore.accept (c : CheckedStore) (r : Rec) : AcceptResult × CheckedStore :=
  ((rawAccept c.raw r).1, ⟨(rawAccept c.raw r).2, rawAccept_built c.built r⟩)

end ZrdtT
#print axioms ZrdtT.rawAccept_built
-- extensional equality: two stores with the same contents are `=` regardless of history
example (m : Std.ExtTreeMap Zrdt.Digest Nat compare) (a b : Zrdt.Digest) (h : a ≠ b) :
    (m.insert a 1).insert b 2 = (m.insert b 2).insert a 1 := by
  apply Std.ExtTreeMap.ext_getElem?; intro k
  simp only [Std.ExtTreeMap.getElem?_insert, Std.LawfulEqCmp.compare_eq_iff_eq]; grind
