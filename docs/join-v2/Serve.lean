-- Reference copy from the JOIN_PLAN v2 review (2026-11-01). Not built by any lake target.
-- Checked with `lake env lean` against core/ at af76d2f, placed under core/Scratch/. No sorry.
import Zrdt.Provenance
import Zrdt.Commit

/-!
# The responder (scratch): what a member sends another member about its store

The audience of a message is a new top-level `DataMessage` field (201): the ACIs of the members
in the author's view when the message was enqueued. It is NOT field 15 or 200, so it stays in the
committed bytes: `openingMatches` binds it to the record's commit, and through the commit to the
record's digest. Only holders of the opening (the addressees) ever see it.

`serve c held x` answers requester `x`:
* `addressed r o s`: `x` is the author or in `r`'s audience; `o` is the opening, sent only if it
  matches `r.commit` and its OWN committed audience contains `x`; `s` the original sender-key
  message, sent only with such an opening;
* `after r`: `r` reaches an addressed record (it is causally after something sent to `x`); its
  structure, never content;
* `boundary d`: the audience is known, `x` is not in it, and `r` reaches nothing addressed to `x`;
  the digest only;
* nothing: audience unknown and not after anything addressed to `x` (ask someone else).
-/

namespace Zrdt
namespace Serve

/-- The field that carries the audience. -/
def audienceField : Nat := 201

/-- The value bytes of length-delimited field `f` of `m`. -/
def fieldValue (m : ByteArray) (f : Field) : Option ByteArray := do
  let (key, p) ← readVarint m f.start
  guard (key &&& 7 = 2)
  let (len, q) ← readVarint m p
  guard (q + len ≤ m.size)
  pure (m.extract q (q + len))

/-- Packed account ids, 16 bytes each. -/
def parseAcis (b : ByteArray) : Option (Array Aci) :=
  if b.size % 16 = 0 then
    (List.range (b.size / 16)).toArray.mapM fun i => Aci.ofBytes? (b.extract (16 * i) (16 * i + 16))
  else none

/-- The audience committed in an opening: exactly one field 201 in its committed bytes. -/
def audienceOf (o : ByteArray) : Option (Array Aci) := do
  let (_, m) ← splitOpening o
  let fs ← fields m
  match (fs.filter (·.num == audienceField)).toList with
  | [f] => parseAcis (← fieldValue m f)
  | _ => none

/-- `x` may see `r`'s content: it wrote it, or it is in the audience. -/
def entitled (x : Aci) (r : Rec) (aud : Option (Array Aci)) : Bool :=
  x == r.author || aud.any (·.contains x)

/-- The opening `o` may go to `x`: it opens `r`, and its own committed audience entitles `x`. -/
def serveOpening (x : Aci) (r : Rec) (o : ByteArray) : Bool :=
  openingMatches r.group r.author r.commit o && entitled x r (audienceOf o)

/-- What the host holds outside the store for one record. -/
structure Held where
  /-- The opening, if this device still holds the content. -/
  opening : Option ByteArray := none
  /-- The audience, cached from an opening checked earlier (kept after the content is erased). -/
  audience : Option (Array Aci) := none
  /-- The original sender-key message bytes, if kept. -/
  skm : Option ByteArray := none

/-- The audience the responder knows for `r`: from a matching opening, else the cache. -/
def audienceFor (r : Rec) (h : Held) : Option (Array Aci) :=
  match h.opening with
  | some o => if openingMatches r.group r.author r.commit o then audienceOf o else h.audience
  | none => h.audience

/-- One item of a reply. -/
inductive Entry
  | addressed (r : Rec) (opening : Option ByteArray) (skm : Option ByteArray)
  | after (r : Rec)
  | boundary (d : Digest)

/-- The reply to requester `x` (a catch-up: the whole view). -/
def serve (c : CheckedStore) (held : Std.ExtTreeMap Digest Held compare) (x : Aci) :
    List Entry :=
  let all := c.raw.map.toList
  let info := fun d => held.getD d {}
  let visD := all.filterMap fun (d, r) =>
    if entitled x r (audienceFor r (info d)) then some d else none
  -- Records that reach an addressed record: walk the links backwards from them.
  let up : DigestSet := walk id (linkedBy c) ∅ visD
  let linkedByUp : DigestSet := up.toList.foldl (init := ∅) fun s d =>
    match c.get d with
    | some r => r.links.foldl (fun s l => s.insert l) s
    | none => s
  all.filterMap fun (d, r) =>
    let h := info d
    if entitled x r (audienceFor r h) then
      let o := h.opening.filter (serveOpening x r)
      some (.addressed r o (if o.isSome then h.skm else none))
    else if up.contains d then some (.after r)
    else if (audienceFor r h).isSome && (linkedByUp.contains d || c.heads.contains d) then
      some (.boundary d)
    else none

/-! ## What the reply may contain -/

/-- **Content goes only where its author sent it.** Every opening in a reply to `x` opens a stored
record (it matches the record's commit, so its audience is the one the author committed), and
`x` is the author or in that audience. Every sender-key message travels with such an opening. -/
theorem serve_content {c : CheckedStore} {held : Std.ExtTreeMap Digest Held compare} {x : Aci}
    {r : Rec} {o : Option ByteArray} {s : Option ByteArray}
    (he : Entry.addressed r o s ∈ serve c held x) :
    (∃ d, c.get d = some r) ∧ (s.isSome → o.isSome) ∧
      ∀ op, o = some op → openingMatches r.group r.author r.commit op = true ∧
        (x = r.author ∨ ∃ aud, audienceOf op = some aud ∧ aud.contains x) := by
  simp only [serve, List.mem_filterMap] at he
  obtain ⟨⟨d, r'⟩, hmem, hf⟩ := he
  have hget : c.get d = some r' := by
    simpa [CheckedStore.get] using Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some.1 hmem
  split at hf
  · simp only [Option.some.injEq, Entry.addressed.injEq] at hf
    obtain ⟨rfl, rfl, rfl⟩ := hf
    refine ⟨⟨d, hget⟩, ?_, ?_⟩
    · intro hs
      split at hs
      · assumption
      · simp at hs
    · intro op hop
      have hsv : serveOpening x r' op = true := by
        cases hh : (held.getD d {}).opening with
        | none => simp [hh] at hop
        | some o' =>
          rw [hh] at hop
          simp only [Option.filter] at hop
          split at hop
          · cases hop; assumption
          · simp at hop
      simp only [serveOpening, entitled, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq,
        Option.any_eq_true] at hsv
      obtain ⟨hm, hx⟩ := hsv
      refine ⟨hm, ?_⟩
      rcases hx with hx | ⟨aud, ha, hc⟩
      · exact .inl hx
      · exact .inr ⟨aud, ha, hc⟩
  · split at hf
    · simp at hf
    · split at hf <;> simp at hf

/-- **Structure without content** goes only for records that reach an addressed record (the walk
from the addressed records; `mem_reachersOf` in `ClassifyFast.lean` says what it holds). -/
theorem serve_after {c : CheckedStore} {held : Std.ExtTreeMap Digest Held compare} {x : Aci}
    {r : Rec} (he : Entry.after r ∈ serve c held x) :
    ∃ d, c.get d = some r ∧
      d ∈ walk id (linkedBy c) ∅ (c.raw.map.toList.filterMap fun (d, r) =>
        if entitled x r (audienceFor r (held.getD d {})) then some d else none) := by
  simp only [serve, List.mem_filterMap] at he
  obtain ⟨⟨d, r'⟩, hmem, hf⟩ := he
  have hget : c.get d = some r' := by
    simpa [CheckedStore.get] using Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some.1 hmem
  split at hf
  · simp at hf
  · split at hf
    · rename_i hup
      simp only [Option.some.injEq, Entry.after.injEq] at hf
      subst hf
      exact ⟨d, hget, Std.ExtTreeSet.contains_iff_mem.1 hup⟩
    · split at hf <;> simp at hf

/-- **A boundary digest hides nothing addressed to `x`.** It is a stored record whose audience
is known and excludes `x`, that `x` did not write, and that is outside the walk from the
addressed records (so it reaches none of them). -/
theorem serve_boundary {c : CheckedStore} {held : Std.ExtTreeMap Digest Held compare} {x : Aci}
    {d : Digest} (he : Entry.boundary d ∈ serve c held x) :
    ∃ r, c.get d = some r ∧ x ≠ r.author ∧
      (∃ aud, audienceFor r (held.getD d {}) = some aud ∧ aud.contains x = false) ∧
      d ∉ walk id (linkedBy c) ∅ (c.raw.map.toList.filterMap fun (d, r) =>
        if entitled x r (audienceFor r (held.getD d {})) then some d else none) := by
  simp only [serve, List.mem_filterMap] at he
  obtain ⟨⟨d', r⟩, hmem, hf⟩ := he
  have hget : c.get d' = some r := by
    simpa [CheckedStore.get] using Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some.1 hmem
  split at hf
  · simp at hf
  · rename_i hne
    split at hf
    · simp at hf
    · rename_i hup
      split at hf
      · rename_i hknown
        simp only [Option.some.injEq, Entry.boundary.injEq] at hf
        subst hf
        refine ⟨r, hget, ?_, ?_, ?_⟩
        · intro hx; apply hne; simp [entitled, hx]
        · simp only [Bool.and_eq_true, Option.isSome_iff_exists] at hknown
          obtain ⟨⟨aud, ha⟩, -⟩ := hknown
          refine ⟨aud, ha, ?_⟩
          simp only [entitled, ha, Option.any_some, Bool.or_eq_true, beq_iff_eq, not_or] at hne
          simpa using hne.2
        · intro hm
          exact hup (Std.ExtTreeSet.contains_iff_mem.2 hm)
      · simp at hf

end Serve
end Zrdt

#print axioms Zrdt.Serve.serve_content
#print axioms Zrdt.Serve.serve_after
#print axioms Zrdt.Serve.serve_boundary
