import Zrdt.Store

/-!
# The relative store: a newcomer's store with an opaque boundary (docs/JOIN_PLAN.md §6.2)

A member added to a group with history gets the records he was sent, the records written after
them, and only the **digests** of the older records they link. His store is *relative*: some links
point to digests he holds no record for. Those digests form the store's **boundary**. Each one was
given to him by a named member, its **voucher** (the responder whose reply carried it).

- `Boundary`: digest to voucher ACI.
- `AcceptOrderRel B l`: the list can be accepted from the end to the front, each record's links
  being digests of records further down the list or digests of `B`.
- `BuiltRel c B`: what makes a raw store correct relative to the boundary `B`. As `Built`, except
  that a link may also be a digest of `B`, and the heads are the stored digests **and the digests
  of `B`** that no stored record links. `builtRel_empty_iff`: with an empty boundary it is exactly
  `Built`.
- `rawAcceptRel c B r`: `rawAccept`, except that a link is resolved by a stored record or by a
  digest of `B`. `rawAcceptRel_empty`: with an empty boundary it is exactly `rawAccept`.
- `RelStore`: a raw store, a boundary, and the proof of `BuiltRel`. The only ways to change one
  are `accept` (through `rawAcceptRel`), `addBoundary`, and `prune`, which drops boundary digests
  that are stored nowhere and linked by no stored record (`ACCEPT_VIEW` in per-digest mode,
  `Zrdt.Proto`).

**Promotion.** If a record arrives whose digest is a boundary digest, and its links resolve, it is
accepted like any other: from then on the digest is a stored record. The digest stays in `B` (a
boundary only grows), so every record accepted while it was only a digest keeps a valid accept
order, and a store blob reopens (`load_reopens`). The digests a store holds no record for are
`boundaryDigests`; they are what `HEADS`, `SERVE` and the blob's readers mean by "the boundary".

**Proved here** (no Mathlib):

- `rawAcceptRel_built`: `accept` keeps a relative store correct. `addBoundary_built` (by
  construction): adding a boundary digest does too.
- `rawAcceptRel_accepted`, `rawAcceptRel_missing`, `rawAcceptRel_unchanged`, `rawAcceptRel_of_ok`:
  what each result means.
- `acceptAll_sound`, `acceptAll_stuck`: the batch version, relative to the boundary.
- `load_ok`, `load_complete`, `load_reopens`: loading records over a boundary gives exactly those
  records; it succeeds for any store's own records and boundary, and gives back that store.
- `linkable_sub`: the links a relative store's `COMMIT` uses are heads that are stored records in
  the host's `live` set (docs/JOIN_PLAN.md §6.2, containment).
- `prune_built` (by construction), `prune_spec`: dropping unlinked boundary digests keeps the store
  correct, and every boundary digest that stays is old, stored, or linked by a stored record.
- `rawAcceptRel_fst_mono`: a larger boundary keeps `accepted`.

**Closed stores are untouched.** `CheckedStore`, `Built`, `rawAccept` and every theorem about them
are as before. A closed store is the relative store with an empty boundary (`ofChecked`), and a
relative store with an empty boundary is a closed store (`toChecked`).
-/

namespace Zrdt

/-- The boundary of a relative store: each digest, with the ACI of the member that vouched for it
(the responder whose reply carried it). -/
abbrev Boundary := Std.ExtTreeMap Digest Aci compare

open Examples in
example : ((∅ : Boundary).insert (dig 1) alice)[dig 1]? = some alice := by simp

/-- The digests of a boundary, as a set. -/
def keySet (B : Boundary) : DigestSet := Std.ExtTreeSet.ofList B.keys compare

open Examples in
#guard (keySet ((∅ : Boundary).insert (dig 2) alice |>.insert (dig 1) alice)).toList ==
  [dig 1, dig 2]

/-- A digest is in `keySet B` exactly when it is a digest of `B`. -/
theorem mem_keySet {B : Boundary} {d : Digest} : d ∈ keySet B ↔ d ∈ B := by
  simp [keySet]

/-- The stored records reached from the digests `start` by following links, as their digests
(`start` included). A start digest that is not stored is left out (`CheckedStore.reachSet` on any
raw store). -/
def RawStore.reachSet (c : RawStore) (start : Array Digest) : DigestSet :=
  walk (fun r => r.links.toList) c.map ∅ start.toList

/-- `CheckedStore.reachSet` is `RawStore.reachSet` of its data. -/
theorem CheckedStore.reachSet_raw (c : CheckedStore) (start : Array Digest) :
    c.reachSet start = c.raw.reachSet start := rfl

/-- The digests of a list inserted into a set: the set's and the list's. -/
theorem mem_foldl_insert_digests {l : List Digest} {s : DigestSet} {d : Digest} :
    d ∈ l.foldl (·.insert ·) s ↔ d ∈ s ∨ d ∈ l := by
  induction l generalizing s with
  | nil => simp
  | cons x xs ih =>
    rw [List.foldl_cons, ih, Std.ExtTreeSet.mem_insert, Std.LawfulEqCmp.compare_eq_iff_eq,
      List.mem_cons]
    constructor
    · rintro ((rfl | h) | h)
      · exact .inr (.inl rfl)
      · exact .inl h
      · exact .inr (.inr h)
    · rintro (h | rfl | h)
      · exact .inl (.inr h)
      · exact .inl (.inl rfl)
      · exact .inr h

/-- The digests that some stored record links. -/
def RawStore.linkedSet (c : RawStore) : DigestSet :=
  c.map.foldl (init := ∅) fun acc _ r => r.links.foldl (·.insert ·) acc

/-- A digest is in `linkedSet` exactly when a stored record links it. -/
theorem RawStore.mem_linkedSet {c : RawStore} {d : Digest} :
    d ∈ c.linkedSet ↔ ∃ (k : Digest) (r : Rec), c.map[k]? = some r ∧ d ∈ r.links := by
  have step : ∀ (l : List (Digest × Rec)) (s : DigestSet),
      d ∈ l.foldl (fun acc b => b.2.links.foldl (·.insert ·) acc) s ↔
        d ∈ s ∨ ∃ p ∈ l, d ∈ p.2.links := by
    intro l
    induction l with
    | nil => simp
    | cons p rest ih =>
      intro s
      rw [List.foldl_cons, ih, ← Array.foldl_toList, mem_foldl_insert_digests,
        Array.mem_toList_iff]
      constructor
      · rintro ((h | h) | ⟨q, hq, hd⟩)
        · exact .inl h
        · exact .inr ⟨p, List.mem_cons_self, h⟩
        · exact .inr ⟨q, List.mem_cons_of_mem _ hq, hd⟩
      · rintro (h | ⟨q, hq, hd⟩)
        · exact .inl (.inl h)
        · rcases List.mem_cons.mp hq with rfl | hq
          · exact .inl (.inr hd)
          · exact .inr ⟨q, hq, hd⟩
  rw [linkedSet, Std.ExtTreeMap.foldl_eq_foldl_toList, step]
  simp only [Std.ExtTreeSet.not_mem_empty, false_or]
  constructor
  · rintro ⟨⟨k, r⟩, hp, hd⟩
    exact ⟨k, r, Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some.mp hp, hd⟩
  · rintro ⟨k, r, hk, hd⟩
    exact ⟨(k, r), Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some.mpr hk, hd⟩

open Examples in
#guard (RawStore.linkedSet ⟨group, ((∅ : RecMap).insert (hashRecord b1) b1).insert
  (hashRecord c1) c1, ∅⟩).toList == [hashRecord a1]

/-! ## Accept order and correctness, relative to a boundary -/

/-- `AcceptOrderRel B l`: the list is newest first, and every link of a record is the digest of a
record further down the list, or a digest of `B`. -/
inductive AcceptOrderRel (B : Boundary) : List Rec → Prop
  /-- The empty list. -/
  | nil : AcceptOrderRel B []
  /-- A record whose links are digests of `B` or of older records, on top of an accept order. -/
  | cons {r : Rec} {older : List Rec} :
      (∀ d ∈ r.links, d ∈ B ∨ ∃ r' ∈ older, hashRecord r' = d) → AcceptOrderRel B older →
      AcceptOrderRel B (r :: older)

/-- With an empty boundary, a relative accept order is an accept order. -/
theorem acceptOrderRel_empty_iff {l : List Rec} : AcceptOrderRel ∅ l ↔ AcceptOrder l := by
  constructor
  · intro h
    induction h with
    | nil => exact .nil
    | cons hr _ ih =>
      exact .cons (fun d hd => (hr d hd).resolve_left (by simp)) ih
  · intro h
    induction h with
    | nil => exact .nil
    | cons hr _ ih => exact .cons (fun d hd => .inr (hr d hd)) ih

/-- A larger boundary keeps an accept order. -/
theorem AcceptOrderRel.mono {B B' : Boundary} (hB : ∀ d ∈ B, d ∈ B') {l : List Rec}
    (h : AcceptOrderRel B l) : AcceptOrderRel B' l := by
  induction h with
  | nil => exact .nil
  | cons hr _ ih => exact .cons (fun d hd => (hr d hd).imp (hB d) id) ih

/-- A smaller boundary keeps an accept order, if it keeps every boundary digest the order's
records link. -/
theorem AcceptOrderRel.restrict {B B' : Boundary} {l : List Rec}
    (hB : ∀ r ∈ l, ∀ d ∈ r.links, d ∈ B → d ∈ B') (h : AcceptOrderRel B l) :
    AcceptOrderRel B' l := by
  induction h with
  | nil => exact .nil
  | @cons r older hr _ ih =>
    refine .cons (fun d hd => (hr d hd).imp (hB r List.mem_cons_self d hd) id)
      (ih fun x hx => hB x (List.mem_cons_of_mem _ hx))

/-- Every link of an accept order is a digest of the boundary or of a record in it. -/
theorem AcceptOrderRel.links {B : Boundary} {l : List Rec} (h : AcceptOrderRel B l) :
    ∀ r ∈ l, ∀ d ∈ r.links, d ∈ B ∨ ∃ r' ∈ l, hashRecord r' = d := by
  induction h with
  | nil => simp
  | cons hr _ ih =>
    intro x hx d hd
    rcases List.mem_cons.mp hx with rfl | hx
    · exact (hr d hd).imp id fun ⟨r', hr', he⟩ => ⟨r', List.mem_cons_of_mem _ hr', he⟩
    · exact (ih x hx d hd).imp id fun ⟨r', hr', he⟩ => ⟨r', List.mem_cons_of_mem _ hr', he⟩

/-- Every record of an accept order is stored, if each record of the order whose links are stored
or in the boundary is itself stored. -/
theorem AcceptOrderRel.all_stored {B : Boundary} {m : RecMap} {l : List Rec}
    (hl : AcceptOrderRel B l)
    (hstep : ∀ x ∈ l, (∀ d ∈ x.links, d ∈ m ∨ d ∈ B) → m[hashRecord x]? = some x) :
    ∀ x ∈ l, m[hashRecord x]? = some x := by
  induction hl with
  | nil => simp
  | @cons r older hr _ ih =>
    have ih' := ih (fun x hx => hstep x (List.mem_cons_of_mem _ hx))
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · apply hstep x List.mem_cons_self
      intro d hd
      rcases hr d hd with hb | ⟨r', hr', rfl⟩
      · exact .inr hb
      · exact .inl (Std.ExtTreeMap.mem_iff_isSome_getElem?.mpr (by simp [ih' r' hr']))
    · exact ih' x hx

/-- What makes a raw store correct relative to the boundary `B`. -/
structure BuiltRel (c : RawStore) (B : Boundary) : Prop where
  /-- Every record is stored under its own digest. -/
  hash_eq : ∀ (k : Digest) (r : Rec), c.map[k]? = some r → hashRecord r = k
  /-- Every record belongs to the store's chat. -/
  group_eq : ∀ (k : Digest) (r : Rec), c.map[k]? = some r → r.group = c.group
  /-- The heads are exactly the stored digests and the boundary digests that no stored record
  links. -/
  heads_iff : ∀ d, d ∈ c.heads ↔
    (d ∈ c.map ∨ d ∈ B) ∧ ∀ (k : Digest) (r : Rec), c.map[k]? = some r → d ∉ r.links
  /-- The records can be listed in an accept order relative to `B`, and that list holds exactly
  the stored records. -/
  order : ∃ l, AcceptOrderRel B l ∧ ∀ r, r ∈ l ↔ ∃ k : Digest, c.map[k]? = some r
  /-- The store holds fewer than `maxRecords` records. -/
  size_lt : c.map.size < maxRecords
  /-- The boundary holds fewer than `maxRecords` digests. -/
  boundary_lt : B.size < maxRecords
  /-- Every record has at most `maxLinks` links. -/
  wellSized : ∀ (k : Digest) (r : Rec), c.map[k]? = some r → r.WellSized

/-- **A closed store is a relative store with an empty boundary**, and the other way round. -/
theorem builtRel_empty_iff {c : RawStore} : BuiltRel c ∅ ↔ Built c := by
  constructor
  · intro h
    exact ⟨h.hash_eq, h.group_eq, fun d => by simpa using h.heads_iff d,
      let ⟨l, hl, hm⟩ := h.order; ⟨l, acceptOrderRel_empty_iff.mp hl, hm⟩, h.size_lt,
      h.wellSized⟩
  · intro h
    exact ⟨h.hash_eq, h.group_eq, fun d => by simpa using h.heads_iff d,
      let ⟨l, hl, hm⟩ := h.order; ⟨l, acceptOrderRel_empty_iff.mpr hl, hm⟩, h.size_lt,
      by simp [maxRecords], h.wellSized⟩

/-- In a correct relative store, every link of every record is a stored digest or a boundary
digest (nothing else is missing). -/
theorem BuiltRel.closed {c : RawStore} {B : Boundary} (h : BuiltRel c B) :
    ∀ (k : Digest) (r : Rec), c.map[k]? = some r → ∀ d ∈ r.links, d ∈ c.map ∨ d ∈ B := by
  intro k r hk d hd
  obtain ⟨l, hl, hmem⟩ := h.order
  rcases hl.links r ((hmem r).mpr ⟨k, hk⟩) d hd with hb | ⟨r', hr', he⟩
  · exact .inr hb
  · obtain ⟨k', hk'⟩ := (hmem r').mp hr'
    have := h.hash_eq k' r' hk'
    subst he; subst this
    exact .inl (Std.ExtTreeMap.mem_iff_isSome_getElem?.mpr (by simp [hk']))

/-- A larger boundary keeps a relative store correct, if the new digests are heads: stored
nowhere and linked by nothing (`heads` must then list them too). -/
theorem BuiltRel.heads_of_mem {c : RawStore} {B : Boundary} (h : BuiltRel c B) {d : Digest}
    (hb : d ∈ B) (hnl : ∀ (k : Digest) (r : Rec), c.map[k]? = some r → d ∉ r.links) :
    d ∈ c.heads :=
  (h.heads_iff d).mpr ⟨.inr hb, hnl⟩

/-! ## Accepting one record, relative to a boundary -/

/-- The links of `r` that are neither stored nor boundary digests, in order. -/
def missingLinksRel (m : RecMap) (B : Boundary) (r : Rec) : Array Digest :=
  r.links.filter (fun l => !m.contains l && !B.contains l)

/-- A link is missing exactly when it is a link of `r`, not stored, and not in the boundary. -/
theorem mem_missingLinksRel {m : RecMap} {B : Boundary} {r : Rec} {d : Digest} :
    d ∈ missingLinksRel m B r ↔ d ∈ r.links ∧ d ∉ m ∧ d ∉ B := by
  rw [missingLinksRel, Array.mem_filter, Std.ExtTreeMap.mem_iff_contains,
    Std.ExtTreeMap.mem_iff_contains]
  cases m.contains d <;> cases B.contains d <;> simp

/-- The missing links are sorted, like the links. -/
theorem missingLinksRel_sorted {m : RecMap} {B : Boundary} {r : Rec} :
    StrictlySorted (missingLinksRel m B r) := by
  unfold StrictlySorted missingLinksRel
  rw [Array.toList_filter]
  exact r.links_sorted.filter _

/-- With an empty boundary, the missing links are those of `missingLinks`. -/
theorem missingLinksRel_empty {m : RecMap} {r : Rec} :
    missingLinksRel m ∅ r = missingLinks m r := by
  simp [missingLinksRel, missingLinks]

/-- Whether the record `r` with digest `d`, once added, is a head: `r` does not link its own
digest, and no stored record links `d`. Stored records can only link `d` if it is a boundary
digest, and then they do exactly when `d` is not a head yet. -/
def headOnArrival (heads : DigestSet) (B : Boundary) (r : Rec) (d : Digest) : Bool :=
  !r.links.contains d && (!B.contains d || heads.contains d)

/-- `headOnArrival`, as a statement. -/
theorem headOnArrival_iff {hs : DigestSet} {B : Boundary} {r : Rec} {d : Digest} :
    headOnArrival hs B r d = true ↔ d ∉ r.links ∧ (d ∉ B ∨ d ∈ hs) := by
  unfold headOnArrival
  rw [Std.ExtTreeMap.mem_iff_contains, Std.ExtTreeSet.mem_iff_contains, ← Array.contains_iff_mem]
  cases r.links.contains d <;> cases B.contains d <;> cases hs.contains d <;> simp

/-- Accept one record into a raw store relative to the boundary `B` (see the module header). The
checks, in order, as `rawAccept`: the chat; the number of links; whether the digest is already
stored (the same record: accepted, nothing changes; a different one: collision); whether the store
is full; whether every link is stored or a boundary digest. -/
def rawAcceptRel (c : RawStore) (B : Boundary) (r : Rec) : AcceptResult × RawStore :=
  if r.group ≠ c.group then (.wrongChat, c)
  else if ¬ r.WellSized then (.tooLarge, c)
  else
    let d := hashRecord r
    match c.map[d]? with
    | some old => if old = r then (.accepted d, c) else (.collision d, c)
    | none =>
      if maxRecords ≤ c.map.size + 1 then (.tooLarge, c)
      else
        let missing := missingLinksRel c.map B r
        if missing.isEmpty then
          let hs := dropLinks c.heads r.links
          (.accepted d, { c with map := c.map.insert d r,
                                 heads := if headOnArrival c.heads B r d then hs.insert d else hs })
        else (.missing missing, c)

/-- **With an empty boundary, `rawAcceptRel` is `rawAccept`.** -/
theorem rawAcceptRel_empty (c : RawStore) (r : Rec) : rawAcceptRel c ∅ r = rawAccept c r := by
  unfold rawAcceptRel rawAccept
  simp only [missingLinksRel_empty]
  by_cases hg : r.group ≠ c.group
  · simp [hg]
  by_cases hw : ¬ r.WellSized
  · simp [hg, hw]
  simp only [hg, hw, ↓reduceIte]
  cases hd : c.map[hashRecord r]? with
  | some old => rfl
  | none =>
    by_cases hf : maxRecords ≤ c.map.size + 1
    · simp only [hf, ↓reduceIte]
    by_cases hm : (missingLinks c.map r).isEmpty = true
    · have hnot : hashRecord r ∉ r.links := by
        intro hx
        have hmem : hashRecord r ∈ c.map := by
          refine Classical.byContradiction fun hx' => ?_
          have : hashRecord r ∈ missingLinks c.map r := mem_missingLinks.mpr ⟨hx, hx'⟩
          simp_all [Array.isEmpty_iff]
        simp [Std.ExtTreeMap.mem_iff_isSome_getElem?, hd] at hmem
      simp [hf, hm, headOnArrival, hnot]
    · simp only [hf, hm, ↓reduceIte, Bool.false_eq_true]

/-- Accepting keeps a raw store correct relative to the boundary. -/
theorem rawAcceptRel_built {c : RawStore} {B : Boundary} (h : BuiltRel c B) (r : Rec) :
    BuiltRel (rawAcceptRel c B r).2 B := by
  unfold rawAcceptRel
  by_cases hg : r.group ≠ c.group
  · simpa [hg] using h
  simp only [hg, ite_false]
  by_cases hw : ¬ r.WellSized
  · simpa [hw] using h
  simp only [hw, ite_false]
  split
  · split <;> exact h
  · rename_i hnone
    split
    · exact h
    rename_i hfull
    split
    · rename_i hmiss
      have hres : ∀ x ∈ r.links, x ∈ c.map ∨ x ∈ B := by
        intro x hx
        refine Classical.byContradiction fun hx' => ?_
        rw [not_or] at hx'
        have : x ∈ missingLinksRel c.map B r := mem_missingLinksRel.mpr ⟨hx, hx'.1, hx'.2⟩
        simp_all [Array.isEmpty_iff]
      have hcl := h.closed
      have hdnot : hashRecord r ∉ c.map := by
        simp [Std.ExtTreeMap.mem_iff_isSome_getElem?, hnone]
      -- The stored records of the new map that link `x`: the old ones, and `r`.
      have hnew : ∀ x, (∀ (k : Digest) (y : Rec), (c.map.insert (hashRecord r) r)[k]? = some y →
          x ∉ y.links) ↔
          (∀ (k : Digest) (y : Rec), c.map[k]? = some y → x ∉ y.links) ∧ x ∉ r.links := by
        intro x
        constructor
        · intro hall
          refine ⟨fun k y hk => hall k y ?_, hall (hashRecord r) r (by simp)⟩
          have hk' : hashRecord r ≠ k := by rintro rfl; simp [hnone] at hk
          simp [Std.ExtTreeMap.getElem?_insert, hk', hk]
        · rintro ⟨hold, hr⟩ k y hk
          rw [Std.ExtTreeMap.getElem?_insert] at hk
          split at hk
          · cases hk; exact hr
          · exact hold k y hk
      -- `headOnArrival` says exactly that the new digest is linked by nothing.
      have hhead : headOnArrival c.heads B r (hashRecord r) = true ↔
          (∀ (k : Digest) (y : Rec), c.map[k]? = some y → hashRecord r ∉ y.links) ∧
            hashRecord r ∉ r.links := by
        rw [headOnArrival_iff]
        constructor
        · rintro ⟨hnl, hb | hh⟩
          · refine ⟨fun k y hk hl => ?_, hnl⟩
            rcases hcl k y hk _ hl with hm | hb'
            · exact hdnot hm
            · simp_all
          · exact ⟨((h.heads_iff _).mp hh).2, hnl⟩
        · rintro ⟨hold, hnl⟩
          refine ⟨hnl, ?_⟩
          by_cases hb : hashRecord r ∈ B
          · exact .inr ((h.heads_iff _).mpr ⟨.inr hb, hold⟩)
          · exact .inl hb
      dsimp only
      refine ⟨?_, ?_, ?_, ?_, ?_, h.boundary_lt, ?_⟩
      · intro k x hk
        rw [Std.ExtTreeMap.getElem?_insert] at hk
        split at hk
        · rename_i he; cases hk; simpa using he
        · exact h.hash_eq k x hk
      · intro k x hk
        rw [Std.ExtTreeMap.getElem?_insert] at hk
        split at hk
        · cases hk; simpa using hg
        · exact h.group_eq k x hk
      · intro x
        rw [hnew x, Std.ExtTreeMap.mem_insert, Std.LawfulEqCmp.compare_eq_iff_eq]
        by_cases hx : x = hashRecord r
        · subst hx
          split
          · rename_i hh
            simp only [Std.ExtTreeSet.mem_insert, Std.LawfulEqCmp.compare_eq_iff_eq, true_or,
              true_and, true_iff]
            exact hhead.mp hh
          · rename_i hh
            simp only [mem_dropLinks, true_or, true_and]
            constructor
            · rintro ⟨hd, hnl⟩
              exact absurd (hhead.mpr ⟨((h.heads_iff _).mp hd).2, hnl⟩) hh
            · intro hx
              exact absurd (hhead.mpr hx) hh
        · have hx' : ¬ hashRecord r = x := fun h' => hx h'.symm
          have hset : x ∈ (if headOnArrival c.heads B r (hashRecord r) = true then
              (dropLinks c.heads r.links).insert (hashRecord r) else dropLinks c.heads r.links) ↔
              x ∈ dropLinks c.heads r.links := by
            split <;> simp [Std.ExtTreeSet.mem_insert, Std.LawfulEqCmp.compare_eq_iff_eq, hx']
          rw [hset, mem_dropLinks, h.heads_iff]
          simp only [hx', false_or, and_assoc]
      · obtain ⟨l, hl, hmem⟩ := h.order
        refine ⟨r :: l, .cons (fun d hd => ?_) hl, fun x => ?_⟩
        · rcases hres d hd with hdm | hb
          · obtain ⟨x, hx⟩ : ∃ x, c.map[d]? = some x :=
              Option.isSome_iff_exists.mp (Std.ExtTreeMap.mem_iff_isSome_getElem?.mp hdm)
            exact .inr ⟨x, (hmem x).mpr ⟨d, hx⟩, h.hash_eq d x hx⟩
          · exact .inl hb
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
      · rw [Std.ExtTreeMap.size_insert]
        split <;> omega
      · intro k x hk
        rw [Std.ExtTreeMap.getElem?_insert] at hk
        split at hk
        · cases hk; simpa using hw
        · exact h.wellSized k x hk
    · exact h

/-! ### What `rawAcceptRel` does, case by case -/

/-- Accepted: `d` is the record's digest, and the record is now stored under it (it may have been
stored already; the map is the same then). -/
theorem rawAcceptRel_accepted {c c' : RawStore} {B : Boundary} {r : Rec} {d : Digest}
    (h : rawAcceptRel c B r = (.accepted d, c')) :
    d = hashRecord r ∧ c'.group = c.group ∧ c'.map = c.map.insert d r ∧
      ∀ old, c.map[d]? = some old → old = r := by
  unfold rawAcceptRel at h
  dsimp only at h
  split at h
  · simp at h
  split at h
  · simp at h
  split at h
  · rename_i old hold
    split at h
    · rename_i heq
      simp only [Prod.mk.injEq, AcceptResult.accepted.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨rfl, rfl, ?_, fun o ho => by rw [hold] at ho; cases ho; exact heq⟩
      subst heq
      apply Std.ExtTreeMap.ext_getElem?
      intro k
      rw [Std.ExtTreeMap.getElem?_insert]
      split
      · rename_i hk
        rw [Std.LawfulEqCmp.compare_eq_iff_eq] at hk
        rw [← hk, hold]
      · rfl
    · simp at h
  · rename_i hnone
    split at h
    · simp at h
    split at h
    · obtain ⟨⟨⟩, rfl⟩ := Prod.mk.inj h
      exact ⟨rfl, rfl, rfl, by simp [hnone]⟩
    · simp at h

/-- Every result other than `accepted` leaves the store as it was. -/
theorem rawAcceptRel_unchanged {c : RawStore} {B : Boundary} {r : Rec}
    (h : ∀ d, (rawAcceptRel c B r).1 ≠ .accepted d) : (rawAcceptRel c B r).2 = c := by
  unfold rawAcceptRel at h ⊢
  dsimp only at h ⊢
  split
  · rfl
  split
  · rfl
  split
  · split
    · rename_i old hold heq
      simp [*] at h
    · rfl
  · split
    · rfl
    split
    · simp [*] at h
    · rfl

/-- Missing: the list is exactly the links that are neither stored nor boundary digests; it is
not empty, and it is sorted. -/
theorem rawAcceptRel_missing {c c' : RawStore} {B : Boundary} {r : Rec} {ds : Array Digest}
    (h : rawAcceptRel c B r = (.missing ds, c')) :
    c' = c ∧ ds ≠ #[] ∧ (∀ x, x ∈ ds ↔ x ∈ r.links ∧ x ∉ c.map ∧ x ∉ B) ∧ StrictlySorted ds := by
  have hc : c' = c := by
    have := rawAcceptRel_unchanged (c := c) (B := B) (r := r) (by simp [h])
    rwa [h] at this
  unfold rawAcceptRel at h
  dsimp only at h
  split at h
  · simp at h
  split at h
  · simp at h
  split at h
  · split at h <;> simp at h
  · split at h
    · simp at h
    split at h
    · simp at h
    · rename_i hne
      obtain ⟨⟨⟩, rfl⟩ := Prod.mk.inj h
      refine ⟨rfl, ?_, fun x => mem_missingLinksRel, missingLinksRel_sorted⟩
      intro he
      simp [he] at hne

/-- A record of the right chat, with few enough links, whose links are all stored or boundary
digests, and whose digest holds no other record, is accepted, unless it is new and the store is
full. -/
theorem rawAcceptRel_of_ok {c : RawStore} {B : Boundary} {r : Rec} (hg : r.group = c.group)
    (hw : r.WellSized) (hl : ∀ x ∈ r.links, x ∈ c.map ∨ x ∈ B)
    (hc : ∀ old, c.map[hashRecord r]? = some old → old = r)
    (hroom : hashRecord r ∉ c.map → c.map.size + 1 < maxRecords) :
    (rawAcceptRel c B r).1 = .accepted (hashRecord r) := by
  unfold rawAcceptRel
  dsimp only
  simp only [hg, ne_eq, not_true_eq_false, ↓reduceIte, hw]
  split
  · rename_i old hold
    simp [hc old hold]
  · rename_i hnone
    have hroom' := hroom (by simp [Std.ExtTreeMap.mem_iff_isSome_getElem?, hnone])
    have hfull : ¬ maxRecords ≤ c.map.size + 1 := by omega
    have hmiss : (missingLinksRel c.map B r).isEmpty = true := by
      rw [Array.isEmpty_iff, Array.eq_empty_iff_forall_not_mem]
      intro x hx
      obtain ⟨hx, hxm, hxb⟩ := mem_missingLinksRel.mp hx
      rcases hl x hx with h' | h'
      · exact hxm h'
      · exact hxb h'
    simp [hfull, hmiss]

/-- **What `rawAcceptRel` answers does not depend on the heads, and a larger boundary keeps
`accepted`.** Two raw stores with the same records and chat, the second boundary holding every
digest of the first: if the first says `accepted d`, so does the second. -/
theorem rawAcceptRel_fst_mono {c c' : RawStore} {B B' : Boundary} {r : Rec} {d : Digest}
    (hm : c'.map = c.map) (hg : c'.group = c.group) (hB : ∀ x ∈ B', x ∈ B)
    (h : (rawAcceptRel c' B' r).1 = .accepted d) : (rawAcceptRel c B r).1 = .accepted d := by
  unfold rawAcceptRel at h ⊢
  rw [hm, hg] at h
  dsimp only at h ⊢
  by_cases hgr : r.group ≠ c.group
  · simp [hgr] at h
  by_cases hw : ¬ r.WellSized
  · simp [hgr, hw] at h
  simp only [hgr, hw, ↓reduceIte] at h ⊢
  cases hd : c.map[hashRecord r]? with
  | some old =>
    rw [hd] at h
    by_cases ho : old = r
    · simp only [ho, ↓reduceIte] at h ⊢; exact h
    · simp [ho] at h
  | none =>
    rw [hd] at h
    simp only at h ⊢
    by_cases hfull : maxRecords ≤ c.map.size + 1
    · simp [hfull] at h
    simp only [hfull, ↓reduceIte] at h ⊢
    by_cases hmiss : (missingLinksRel c.map B' r).isEmpty = true
    · have hmiss' : (missingLinksRel c.map B r).isEmpty = true := by
        rw [Array.isEmpty_iff, Array.eq_empty_iff_forall_not_mem] at hmiss ⊢
        intro x hx
        obtain ⟨hx, hxm, hxb⟩ := mem_missingLinksRel.mp hx
        refine hmiss x (mem_missingLinksRel.mpr ⟨hx, hxm, fun hb => hxb (hB x hb)⟩)
      simp only [hmiss, hmiss', ↓reduceIte] at h ⊢
      exact h
    · simp [hmiss] at h

/-! ## The relative store -/

/-- A store together with its boundary and the proof that it is correct relative to it. The only
ways to get one are `empty`, `emptyWith`, `ofChecked`, `accept`, `addBoundary` and the functions
built on them. -/
structure RelStore where
  /-- The records and heads. The heads include the boundary digests no record links. -/
  raw : RawStore
  /-- Every digest this store took as a boundary digest, with its voucher. -/
  boundary : Boundary
  /-- The proof that the data is correct (erased in compiled code). -/
  built : BuiltRel raw boundary

namespace RelStore

/-- Two relative stores with the same data are equal (the proof carries no data). -/
theorem ext {c d : RelStore} (h : c.raw = d.raw) (hb : c.boundary = d.boundary) : c = d := by
  cases c; cases d; cases h; cases hb; rfl

/-- The store of chat `g` with no records and the boundary `B` (fewer than `maxRecords`
digests). Every boundary digest is a head. -/
def emptyWith (g : GroupId) (B : Boundary) (hB : B.size < maxRecords) : RelStore where
  raw := ⟨g, ∅, keySet B⟩
  boundary := B
  built := {
    hash_eq := by simp
    group_eq := by simp
    heads_iff := by simp [mem_keySet]
    order := ⟨[], .nil, by simp⟩
    size_lt := by simp [maxRecords]
    boundary_lt := hB
    wellSized := by simp }

/-- The empty relative store of chat `g`: no records, no boundary. -/
def empty (g : GroupId) : RelStore := emptyWith g ∅ (by simp [maxRecords])

/-- A closed store, as a relative store with an empty boundary. -/
def ofChecked (c : CheckedStore) : RelStore := ⟨c.raw, ∅, builtRel_empty_iff.mpr c.built⟩

/-- A relative store with an empty boundary, as a closed store. -/
def toChecked? (c : RelStore) : Option CheckedStore :=
  if h : c.boundary = ∅ then some ⟨c.raw, builtRel_empty_iff.mp (h ▸ c.built)⟩ else none

/-- Back and forth: a closed store comes back unchanged. -/
theorem toChecked?_ofChecked (c : CheckedStore) : (ofChecked c).toChecked? = some c := by
  simp [toChecked?, ofChecked]

/-- Accept one record (see `rawAcceptRel`). Returns what happened and the new store. The boundary
does not change. -/
def accept (c : RelStore) (r : Rec) : AcceptResult × RelStore :=
  let p := rawAcceptRel c.raw c.boundary r
  (p.1, ⟨p.2, c.boundary, rawAcceptRel_built c.built r⟩)

/-- `accept` reports what `rawAcceptRel` reports. -/
@[simp] theorem accept_fst (c : RelStore) (r : Rec) :
    (c.accept r).1 = (rawAcceptRel c.raw c.boundary r).1 := rfl

/-- `accept`'s new store holds what `rawAcceptRel`'s does. -/
@[simp] theorem accept_raw (c : RelStore) (r : Rec) :
    (c.accept r).2.raw = (rawAcceptRel c.raw c.boundary r).2 := rfl

/-- `accept` keeps the boundary. -/
@[simp] theorem accept_boundary (c : RelStore) (r : Rec) :
    (c.accept r).2.boundary = c.boundary := rfl

/-- Every result other than `accepted` leaves the store as it was. -/
theorem accept_unchanged {c : RelStore} {r : Rec}
    (h : ∀ d, (c.accept r).1 ≠ .accepted d) : (c.accept r).2 = c :=
  ext (rawAcceptRel_unchanged h) rfl

/-- One `accept`: the chat and boundary are the same, every record is kept, and the only record
that can be new is `r`. -/
theorem accept_step (c : RelStore) (r : Rec) :
    (c.accept r).2.raw.group = c.raw.group ∧
    (∀ (k : Digest) (x : Rec), c.raw.map[k]? = some x → (c.accept r).2.raw.map[k]? = some x) ∧
    (∀ (k : Digest) (x : Rec), (c.accept r).2.raw.map[k]? = some x →
      c.raw.map[k]? = some x ∨ x = r) := by
  cases hres : (c.accept r).1 with
  | accepted d =>
    have hraw : rawAcceptRel c.raw c.boundary r = (.accepted d, (c.accept r).2.raw) :=
      Prod.ext (by rw [← accept_fst, hres]) rfl
    obtain ⟨rfl, hg, hmap, hold⟩ := rawAcceptRel_accepted hraw
    refine ⟨hg, fun k x hk => ?_, fun k x hk => ?_⟩
    · rw [hmap, Std.ExtTreeMap.getElem?_insert]
      split
      · rename_i he
        rw [Std.LawfulEqCmp.compare_eq_iff_eq] at he
        subst he
        rw [hold x hk]
      · exact hk
    · rw [hmap, Std.ExtTreeMap.getElem?_insert] at hk
      split at hk
      · cases hk; exact .inr rfl
      · exact .inl hk
  | _ =>
    have := accept_unchanged (c := c) (r := r) (fun d h => by rw [hres] at h; cases h)
    rw [this]
    exact ⟨rfl, fun _ _ h => h, fun _ _ h => .inl h⟩

/-- Adding a digest that is neither stored nor in the boundary, as a new head, keeps the store
correct, if the boundary stays under its limit. -/
theorem addBoundary_built {c : RawStore} {B : Boundary} (h : BuiltRel c B) {d : Digest} (v : Aci)
    (hm : d ∉ c.map) (hb : d ∉ B) (hsize : B.size + 1 < maxRecords) :
    BuiltRel { c with heads := c.heads.insert d } (B.insert d v) where
  hash_eq := h.hash_eq
  group_eq := h.group_eq
  heads_iff := by
    intro x
    simp only [Std.ExtTreeSet.mem_insert, Std.ExtTreeMap.mem_insert,
      Std.LawfulEqCmp.compare_eq_iff_eq]
    by_cases hx : d = x
    · subst hx
      simp only [true_or, or_true, true_and, true_iff]
      intro k r hk hl
      rcases h.closed k r hk d hl with h' | h'
      · exact hm h'
      · exact hb h'
    · simp only [hx, false_or]
      rw [h.heads_iff]
  order := let ⟨l, hl, hmem⟩ := h.order
    ⟨l, hl.mono fun x hx => Std.ExtTreeMap.mem_insert.mpr (.inr hx), hmem⟩
  size_lt := h.size_lt
  boundary_lt := by
    have := Std.ExtTreeMap.size_insert_le (t := B) (k := d) (v := v)
    omega
  wellSized := h.wellSized

/-- Add `d` to the boundary with voucher `v`. Nothing changes if `d` is a stored digest or
already in the boundary (the first voucher stays). `none` if the boundary is full. -/
def addBoundary (c : RelStore) (d : Digest) (v : Aci) : Option RelStore :=
  if hk : d ∈ c.raw.map ∨ d ∈ c.boundary then some c
  else if hs : c.boundary.size + 1 < maxRecords then
    some ⟨{ c.raw with heads := c.raw.heads.insert d }, c.boundary.insert d v,
      addBoundary_built c.built v (fun h => hk (.inl h)) (fun h => hk (.inr h)) hs⟩
  else none

/-- What `addBoundary` did: the records and the chat are the same; `d` is now stored or in the
boundary; the boundary only grew, and only by `d` with voucher `v`. -/
theorem addBoundary_spec {c e : RelStore} {d : Digest} {v : Aci}
    (h : c.addBoundary d v = some e) :
    e.raw.group = c.raw.group ∧ e.raw.map = c.raw.map ∧ (d ∈ e.raw.map ∨ d ∈ e.boundary) ∧
      (∀ (x : Digest) (a : Aci), c.boundary[x]? = some a → e.boundary[x]? = some a) ∧
      (∀ (x : Digest) (a : Aci), e.boundary[x]? = some a →
        c.boundary[x]? = some a ∨ (x = d ∧ a = v)) := by
  unfold addBoundary at h
  split at h
  · rename_i hk
    cases h
    exact ⟨rfl, rfl, hk, fun _ _ h => h, fun _ _ h => .inl h⟩
  · rename_i hk
    split at h
    · cases h
      refine ⟨rfl, rfl, .inr (Std.ExtTreeMap.mem_insert_self), fun x a hx => ?_, fun x a hx => ?_⟩
      · rw [Std.ExtTreeMap.getElem?_insert]
        split
        · rename_i he
          rw [Std.LawfulEqCmp.compare_eq_iff_eq] at he
          subst he
          exact absurd (.inr (Std.ExtTreeMap.mem_iff_isSome_getElem?.mpr (by simp [hx]))) hk
        · exact hx
      · rw [Std.ExtTreeMap.getElem?_insert] at hx
        split at hx
        · rename_i he
          rw [Std.LawfulEqCmp.compare_eq_iff_eq] at he
          cases hx
          exact .inr ⟨he.symm, rfl⟩
        · exact .inl hx
    · cases h

/-- `addBoundary` on each entry, in order. `none` if the boundary fills up. -/
def addBoundaryAll (c : RelStore) : List (Digest × Aci) → Option RelStore
  | [] => some c
  | (d, v) :: rest => (c.addBoundary d v).bind (·.addBoundaryAll rest)

/-- The boundary digests `prune old` drops: not in `old`, not stored, and linked by no stored
record. -/
def pruned (c : RelStore) (old : Boundary) (d : Digest) : Bool :=
  !old.contains d && !c.raw.map.contains d && !c.raw.linkedSet.contains d

/-- What `pruned` means. -/
theorem pruned_iff {c : RelStore} {old : Boundary} {d : Digest} :
    c.pruned old d = true ↔
      d ∉ old ∧ d ∉ c.raw.map ∧ ∀ (k : Digest) (r : Rec), c.raw.map[k]? = some r → d ∉ r.links := by
  rw [pruned, Std.ExtTreeMap.mem_iff_contains (t := old), Std.ExtTreeMap.mem_iff_contains
    (t := c.raw.map)]
  have hl : (∀ (k : Digest) (r : Rec), c.raw.map[k]? = some r → d ∉ r.links) ↔
      c.raw.linkedSet.contains d = false := by
    rw [Bool.eq_false_iff, ne_eq, ← Std.ExtTreeSet.mem_iff_contains, RawStore.mem_linkedSet]
    constructor
    · rintro h ⟨k, r, hk, hd⟩
      exact h k r hk hd
    · intro h k r hk hd
      exact h ⟨k, r, hk, hd⟩
  rw [hl]
  cases old.contains d <;> cases c.raw.map.contains d <;> cases c.raw.linkedSet.contains d <;>
    simp

/-- Dropping boundary digests that are stored nowhere and linked by no stored record keeps the
store correct. -/
theorem prune_built {c : RawStore} {B : Boundary} (h : BuiltRel c B) (drop : Digest → Bool)
    (hdrop : ∀ d, drop d = true → d ∉ c.map ∧
      ∀ (k : Digest) (r : Rec), c.map[k]? = some r → d ∉ r.links) :
    BuiltRel { c with heads := c.heads.filter fun d => !drop d } (B.filter fun d _ => !drop d) where
  hash_eq := h.hash_eq
  group_eq := h.group_eq
  heads_iff := by
    intro x
    simp only [Std.ExtTreeSet.mem_filter, Std.ExtTreeMap.mem_filter, Std.ExtTreeSet.get_eq,
      Std.ExtTreeMap.getKey_eq]
    constructor
    · rintro ⟨hx, hd⟩
      obtain ⟨hmb, hnl⟩ := (h.heads_iff x).mp hx
      exact ⟨hmb.imp id fun hb => ⟨hb, hd⟩, hnl⟩
    · rintro ⟨hmb, hnl⟩
      have hb : x ∈ c.map ∨ x ∈ B := hmb.imp id fun ⟨hb, _⟩ => hb
      refine ⟨(h.heads_iff x).mpr ⟨hb, hnl⟩, ?_⟩
      rcases hmb with hm | ⟨_, hd⟩
      · cases hx : drop x
        · rfl
        · exact absurd hm (hdrop x hx).1
      · exact hd
  order := by
    obtain ⟨l, hl, hmem⟩ := h.order
    refine ⟨l, hl.restrict fun r hr d hd hb => ?_, hmem⟩
    obtain ⟨k, hk⟩ := (hmem r).mp hr
    simp only [Std.ExtTreeMap.mem_filter, Std.ExtTreeMap.getKey_eq]
    refine ⟨hb, ?_⟩
    cases hx : drop d
    · rfl
    · exact absurd hd ((hdrop d hx).2 k r hk)
  size_lt := h.size_lt
  boundary_lt := Nat.lt_of_le_of_lt Std.ExtTreeMap.size_filter_le_size h.boundary_lt
  wellSized := h.wellSized

/-- Drop the boundary digests that are not in `old`, not stored, and linked by no stored record
(`pruned`): `ACCEPT_VIEW` in per-digest mode keeps only the boundary digests a stored record
links (docs/JOIN_PLAN.md §4.4). The records are the same. -/
def prune (c : RelStore) (old : Boundary) : RelStore :=
  ⟨{ c.raw with heads := c.raw.heads.filter fun d => !c.pruned old d },
    c.boundary.filter fun d _ => !c.pruned old d,
    prune_built c.built (c.pruned old) fun _ hd =>
      let h := pruned_iff.mp hd; ⟨h.2.1, h.2.2⟩⟩

/-- **What `prune` does.** The records and the chat are the same. The boundary only shrinks, and a
digest stays exactly when it is not dropped. A boundary digest that stays is in `old`, stored, or
linked by a stored record. -/
theorem prune_spec (c : RelStore) (old : Boundary) :
    (c.prune old).raw.map = c.raw.map ∧ (c.prune old).raw.group = c.raw.group ∧
    (∀ (x : Digest) (a : Aci), (c.prune old).boundary[x]? = some a → c.boundary[x]? = some a) ∧
    (∀ x, x ∈ (c.prune old).boundary → x ∈ old ∨ x ∈ c.raw.map ∨
      ∃ (k : Digest) (r : Rec), c.raw.map[k]? = some r ∧ x ∈ r.links) := by
  refine ⟨rfl, rfl, fun x a hx => ?_, fun x hx => ?_⟩
  · simp only [prune, Std.ExtTreeMap.getElem?_filter'] at hx
    cases hc : c.boundary[x]? with
    | none => rw [hc] at hx; cases hx
    | some b => rw [hc] at hx; simp only [Option.filter] at hx; split at hx <;> simp_all
  · simp only [prune, Std.ExtTreeMap.mem_filter, Std.ExtTreeMap.getKey_eq] at hx
    obtain ⟨_, hnd⟩ := hx
    have hp : c.pruned old x = false := by
      cases hp : c.pruned old x
      · rfl
      · simp [hp] at hnd
    by_cases ho : x ∈ old
    · exact .inl ho
    by_cases hm : x ∈ c.raw.map
    · exact .inr (.inl hm)
    refine .inr (.inr ?_)
    rw [← RawStore.mem_linkedSet, Std.ExtTreeSet.mem_iff_contains]
    rw [Std.ExtTreeMap.mem_iff_contains, Bool.not_eq_true] at ho hm
    simpa [pruned, ho, hm] using hp

open Examples in
-- A digest no record links is dropped; one in `old` stays.
#guard (((empty group).addBoundaryAll [(dig 1, alice), (dig 2, alice)]).map fun c =>
  (c.prune ((∅ : Boundary).insert (dig 2) bob)).boundary.keys) == some [dig 2]

/-! ## Observers -/

/-- The chat the store belongs to. -/
def group (c : RelStore) : GroupId := c.raw.group

/-- The heads: the stored digests and the boundary digests that no stored record links. -/
def heads (c : RelStore) : DigestSet := c.raw.heads

/-- The heads as a sorted array. -/
def headsArray (c : RelStore) : Array Digest := c.heads.toList.toArray

/-- Whether a record with digest `d` is stored. -/
def has (c : RelStore) (d : Digest) : Bool := c.raw.map.contains d

/-- The record with digest `d`, if stored. -/
def get (c : RelStore) (d : Digest) : Option Rec := c.raw.map[d]?

/-- The number of stored records. -/
def size (c : RelStore) : Nat := c.raw.map.size

/-- The stored records, sorted by digest. -/
def records (c : RelStore) : Array Rec := (c.raw.map.toList.map Prod.snd).toArray

/-- The records of a store are the values of its map. -/
theorem mem_records {c : RelStore} {x : Rec} :
    x ∈ c.records ↔ ∃ k : Digest, c.raw.map[k]? = some x := by
  simp only [records, List.mem_toArray, List.mem_map]
  constructor
  · rintro ⟨⟨k, y⟩, hk, rfl⟩
    exact ⟨k, Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some.mp hk⟩
  · rintro ⟨k, hk⟩
    exact ⟨(k, x), Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some.mpr hk, rfl⟩

/-- The boundary digests the store holds no record for, sorted: the store's own boundary in
`SERVE` (`Serve.Me.boundary`). -/
def boundaryDigests (c : RelStore) : DigestSet :=
  Std.ExtTreeSet.ofList (c.boundary.keys.filter (!c.raw.map.contains ·)) compare

/-- A digest is in `boundaryDigests` exactly when it is in the boundary and not stored. -/
theorem mem_boundaryDigests {c : RelStore} {d : Digest} :
    d ∈ c.boundaryDigests ↔ d ∈ c.boundary ∧ d ∉ c.raw.map := by
  rw [Std.ExtTreeMap.mem_iff_contains (k := d) (t := c.raw.map)]
  simp only [boundaryDigests, Std.ExtTreeSet.mem_ofList, List.contains_iff_mem, List.mem_filter,
    Std.ExtTreeMap.mem_keys, Bool.not_eq_true', Bool.not_eq_true]

/-- The stored records reached from the digests `start` by following links, as their digests
(`start` included). A start digest that is not stored, a boundary digest for one, is left out. -/
def reachSet (c : RelStore) (start : Array Digest) : DigestSet := c.raw.reachSet start

/-! ## `LINKABLE`: what a relative store's own records may link (docs/JOIN_PLAN.md §6.2)

A phantom digest (one no member holds a record for) that the holder linked would leave every
later record of his unresolvable at every member. So a relative store's `COMMIT` links only heads
that are stored records the host holds `live` (its own included) or as author copy; the host
passes that set as `live`. Boundary digests and relayed or structure-only heads are left for
others to link. Compare codes still use all heads (`HEADS`). -/

/-- The heads that are stored records in `live`, sorted. -/
def linkable (c : RelStore) (live : DigestSet) : Array Digest :=
  (c.heads.toList.filter fun d => c.raw.map.contains d && live.contains d).toArray

/-- A digest is linkable exactly when it is a head, a stored record, and in `live`. -/
theorem mem_linkable {c : RelStore} {live : DigestSet} {d : Digest} :
    d ∈ c.linkable live ↔ d ∈ c.heads ∧ d ∈ c.raw.map ∧ d ∈ live := by
  rw [Std.ExtTreeMap.mem_iff_contains (k := d) (t := c.raw.map),
    Std.ExtTreeSet.mem_iff_contains (k := d) (t := live)]
  simp [linkable]

/-- **`linkable_sub`: a relative store links only live records.** Every digest `LINKABLE`
returns is a head (no stored record links it), the digest of a stored record (never a boundary
digest), and in the host's `live` set. -/
theorem linkable_sub {c : RelStore} {live : DigestSet} {d : Digest} (h : d ∈ c.linkable live) :
    (∃ r, c.get d = some r) ∧ d ∈ live ∧
      ∀ (k : Digest) (x : Rec), c.raw.map[k]? = some x → d ∉ x.links := by
  obtain ⟨hh, hm, hl⟩ := mem_linkable.mp h
  refine ⟨Option.isSome_iff_exists.mp (Std.ExtTreeMap.mem_iff_isSome_getElem?.mp hm), hl,
    ((c.built.heads_iff d).mp hh).2⟩

/-! ## Accepting many records -/

/-- What a store change `c → e` that adds records from `src` and leaves `left` over guarantees:
the chat and the boundary are the same, `c`'s records are kept, new records come from `src`,
records of `src` not left over are stored under their digest, and left-over records come from
`src`. -/
structure Adds (c e : RelStore) (src left : List Rec) : Prop where
  group_eq : e.group = c.group
  boundary_eq : e.boundary = c.boundary
  keeps : ∀ (k : Digest) (x : Rec), c.raw.map[k]? = some x → e.raw.map[k]? = some x
  only : ∀ (k : Digest) (x : Rec), e.raw.map[k]? = some x → c.raw.map[k]? = some x ∨ x ∈ src
  stored : ∀ x ∈ src, x ∉ left → e.raw.map[hashRecord x]? = some x
  left_sub : ∀ x ∈ left, x ∈ src

/-- Two such changes in a row, where the second works on what the first left over. -/
theorem Adds.trans {c d e : RelStore} {src mid left : List Rec} (h₁ : Adds c d src mid)
    (h₂ : Adds d e mid left) : Adds c e src left where
  group_eq := h₂.group_eq.trans h₁.group_eq
  boundary_eq := h₂.boundary_eq.trans h₁.boundary_eq
  keeps := fun k x hk => h₂.keeps k x (h₁.keeps k x hk)
  only := fun k x hk => by
    rcases h₂.only k x hk with hd | hm
    · exact h₁.only k x hd
    · exact Or.inr (h₁.left_sub x hm)
  stored := fun x hx hl => by
    by_cases hm : x ∈ mid
    · exact h₂.stored x hm hl
    · exact h₂.keeps _ x (h₁.stored x hx hm)
  left_sub := fun x hx => h₁.left_sub x (h₂.left_sub x hx)

/-- Offer each record to `accept` once, in order. Returns the new store and, after `keep`, the
records that were not accepted. -/
def pass (c : RelStore) (keep : Array Rec) : List Rec → RelStore × Array Rec
  | [] => (c, keep)
  | r :: rest =>
    match c.accept r with
    | (.accepted _, c') => pass c' keep rest
    | (_, c') => pass c' (keep.push r) rest

/-- Offer the records to `accept` again and again, until a pass accepts none of them. Returns the
new store and the records never accepted. -/
def retry (c : RelStore) (left : Array Rec) : RelStore × Array Rec :=
  let (c', keep) := pass c #[] left.toList
  if keep.size < left.size then retry c' keep else (c', keep)
termination_by left.size

/-- One `accept` that reports `accepted`, as a store change. -/
theorem Adds.of_accepted {c c' : RelStore} {r : Rec} {d : Digest}
    (hacc : c.accept r = (.accepted d, c')) : Adds c c' [r] [] := by
  have h1 := accept_step c r
  rw [hacc] at h1
  obtain ⟨hg, hkeep, honly⟩ := h1
  have hraw : rawAcceptRel c.raw c.boundary r = (.accepted d, c'.raw) := by
    have e1 : (c.accept r).1 = .accepted d := by rw [hacc]
    have e2 : (c.accept r).2.raw = c'.raw := by rw [hacc]
    rw [accept_fst] at e1
    rw [accept_raw] at e2
    exact Prod.ext e1 e2
  obtain ⟨rfl, -, hmap, -⟩ := rawAcceptRel_accepted hraw
  have hb : c'.boundary = c.boundary := by
    have := accept_boundary c r
    rw [hacc] at this
    exact this
  refine ⟨hg, hb, hkeep, fun k x hk => (honly k x hk).imp id (by rintro rfl; simp),
    fun x hx _ => ?_, by simp⟩
  simp only [List.mem_singleton] at hx
  subst hx
  simp [hmap]

/-- What one pass does. Started with `keep`, it ends with `keep` followed by the records it did
not accept, and it adds the others. If it accepted none, the store is unchanged and `accept`
refuses each of them. -/
theorem pass_spec (c : RelStore) (keep : Array Rec) (l : List Rec) :
    (∃ more : List Rec, (pass c keep l).2 = keep ++ more.toArray ∧
      Adds c (pass c keep l).1 l more ∧ more.length ≤ l.length) ∧
    ((pass c keep l).2.size = keep.size + l.length →
      (pass c keep l).1 = c ∧ ∀ x ∈ l, ∀ d, (c.accept x).1 ≠ .accepted d) := by
  induction l generalizing c keep with
  | nil =>
    refine ⟨⟨[], by simp [pass], ⟨rfl, rfl, fun _ _ h => h, fun _ _ h => Or.inl h,
      by simp, by simp⟩, Nat.le_refl _⟩, fun _ => ⟨rfl, by simp⟩⟩
  | cons r rest ih =>
    simp only [pass]
    split
    · rename_i d c' hacc
      obtain ⟨⟨more, hmore, hadds, hlen⟩, _⟩ := ih c' keep
      have hstep : Adds c c' [r] [] := Adds.of_accepted hacc
      refine ⟨⟨more, hmore, ?_, by simp; omega⟩, fun hsize => ?_⟩
      · refine ⟨hadds.group_eq.trans hstep.group_eq, hadds.boundary_eq.trans hstep.boundary_eq,
          fun k x hk => hadds.keeps k x (hstep.keeps k x hk), fun k x hk => ?_,
          fun x hx hl => ?_, fun x hx => ?_⟩
        · rcases hadds.only k x hk with h' | h'
          · rcases hstep.only k x h' with h'' | h''
            · exact Or.inl h''
            · exact Or.inr (by simp at h''; simp [h''])
          · exact Or.inr (List.mem_cons_of_mem _ h')
        · rcases List.mem_cons.mp hx with rfl | hx'
          · exact hadds.keeps _ x (hstep.stored x (by simp) (by simp))
          · exact hadds.stored x hx' hl
        · exact List.mem_cons_of_mem _ (hadds.left_sub x hx)
      · exfalso
        rw [hmore] at hsize
        simp at hsize
        omega
    · rename_i res c' hres hacc
      have hc' : c' = c := by
        have := accept_unchanged (c := c) (r := r) (by rw [hacc]; exact fun d e => hres d e)
        rwa [hacc] at this
      subst c'
      obtain ⟨⟨more, hmore, hadds, hlen⟩, hstuck⟩ := ih c (keep.push r)
      refine ⟨⟨r :: more, by rw [hmore]; simp, ?_, by simp; omega⟩, fun hsize => ?_⟩
      · refine ⟨hadds.group_eq, hadds.boundary_eq, hadds.keeps, fun k x hk => ?_,
          fun x hx hl => ?_, fun x hx => ?_⟩
        · rcases hadds.only k x hk with h' | h'
          · exact Or.inl h'
          · exact Or.inr (List.mem_cons_of_mem _ h')
        · rcases List.mem_cons.mp hx with rfl | hx'
          · simp at hl
          · exact hadds.stored x hx' (fun h => hl (List.mem_cons_of_mem _ h))
        · rcases List.mem_cons.mp hx with rfl | hx'
          · exact List.mem_cons_self
          · exact List.mem_cons_of_mem _ (hadds.left_sub x hx')
      · have hsize' :
            (pass c (keep.push r) rest).2.size = (keep.push r).size + rest.length := by
          simp at hsize ⊢; omega
        obtain ⟨heq, hrest⟩ := hstuck hsize'
        refine ⟨heq, fun x hx d => ?_⟩
        rcases List.mem_cons.mp hx with rfl | hx'
        · rw [hacc]; exact fun h => hres d h
        · exact hrest x hx' d

/-- What `retry` guarantees: it adds records as `Adds` says, and `accept` refuses every record it
leaves over, in the final store. -/
theorem retry_spec (c : RelStore) (left : Array Rec) :
    Adds c (retry c left).1 left.toList (retry c left).2.toList ∧
      ∀ x ∈ (retry c left).2, ∀ d, ((retry c left).1.accept x).1 ≠ .accepted d := by
  fun_induction retry c left with
  | case1 c left c' keep hpass hlt ih =>
    rw [hpass]
    dsimp only
    simp only [hlt, ↓reduceIte]
    obtain ⟨⟨more, hmore, hadds, _⟩, _⟩ := pass_spec c #[] left.toList
    rw [hpass] at hmore hadds
    dsimp only at hmore hadds
    subst hmore
    simp only [List.toList_toArray, Array.empty_append] at ih hadds ⊢
    exact ⟨hadds.trans ih.1, ih.2⟩
  | case2 c left c' keep hpass hge =>
    rw [hpass]
    dsimp only
    simp only [hge, ↓reduceIte]
    obtain ⟨⟨more, hmore, hadds, hlen⟩, hstuck⟩ := pass_spec c #[] left.toList
    rw [hpass] at hmore hadds hstuck
    dsimp only at hmore hadds hstuck
    subst hmore
    have hsize : (#[] ++ more.toArray).size = (#[] : Array Rec).size + left.toList.length := by
      simp at hge hlen ⊢; omega
    obtain ⟨rfl, hrefuse⟩ := hstuck hsize
    simp only [List.toList_toArray, Array.empty_append] at hadds ⊢
    refine ⟨hadds, fun x hx d => ?_⟩
    have hx' : x ∈ left.toList := hadds.left_sub x (by simpa using hx)
    exact hrefuse x hx' d

/-- `accept` on each record in order: the chat and the boundary are the same, every record is
kept, and new records come from the list. -/
theorem fold_accept (l : List Rec) (c : RelStore) :
    (l.foldl (fun c r => (c.accept r).2) c).raw.group = c.raw.group ∧
    (l.foldl (fun c r => (c.accept r).2) c).boundary = c.boundary ∧
    (∀ (k : Digest) (x : Rec), c.raw.map[k]? = some x →
      (l.foldl (fun c r => (c.accept r).2) c).raw.map[k]? = some x) ∧
    (∀ (k : Digest) (x : Rec), (l.foldl (fun c r => (c.accept r).2) c).raw.map[k]? = some x →
      c.raw.map[k]? = some x ∨ x ∈ l) := by
  induction l generalizing c with
  | nil => exact ⟨rfl, rfl, fun _ _ h => h, fun _ _ h => .inl h⟩
  | cons r rest ih =>
    obtain ⟨hg, hb, hk, ho⟩ := ih (c.accept r).2
    obtain ⟨hg', hk', ho'⟩ := accept_step c r
    simp only [List.foldl_cons]
    refine ⟨hg.trans hg', hb, fun k x h => hk k x (hk' k x h), fun k x h => ?_⟩
    rcases ho k x h with h | h
    · rcases ho' k x h with h | rfl
      · exact .inl h
      · exact .inr List.mem_cons_self
    · exact .inr (List.mem_cons_of_mem _ h)

/-! ### An accept order to try first

`acceptAll` first accepts the batch in an order computed by Kahn's algorithm, then lets `retry`
finish. The order only saves work: whatever it is, `retry` offers every record of the batch
again until nothing more is accepted, so the guarantees do not depend on it. -/

/-- For each record of the batch: how many of its links are neither stored nor boundary digests.
For each such digest: the records (by index) that wait for it. And the records that wait for
nothing, in input order. -/
def planRel (c : RelStore) (rs : Array Rec) :
    Array Nat × Std.ExtTreeMap Digest (List Nat) compare × List Nat :=
  let (counts, waiting, ready) := rs.foldl (init := (#[], ∅, [])) fun (counts, waiting, ready) r =>
    let i := counts.size
    let lacking := r.links.filter (fun l => !c.raw.map.contains l && !c.boundary.contains l)
    (counts.push lacking.size,
     lacking.foldl (fun w l => w.insert l (i :: w.getD l [])) waiting,
     if lacking.isEmpty then i :: ready else ready)
  (counts, waiting, ready.reverse)

/-- Kahn's worklist, without a store: output each ready record, and count down the records that
wait for its digest. -/
def orderLoop (rs : Array Rec) (counts : Array Nat)
    (waiting : Std.ExtTreeMap Digest (List Nat) compare) (out : Array Rec) :
    List Nat → Array Rec
  | [] => out
  | i :: ready =>
    match rs[i]? with
    | none => orderLoop rs counts waiting out ready
    | some r =>
      let d := hashRecord r
      if h : d ∈ waiting then
        let (counts, freed) := CheckedStore.release counts (waiting.get d h)
        orderLoop rs counts (waiting.erase d) (out.push r) (freed ++ ready)
      else orderLoop rs counts waiting (out.push r) ready
termination_by ready => (waiting.size, ready.length)
decreasing_by
  all_goals first
    | exact Prod.Lex.right _ (by simp)
    | exact Prod.Lex.left _ _ (size_erase_lt h)

/-- Everything `orderLoop` outputs was in `out` or is a record of the batch. -/
theorem orderLoop_sub (rs : Array Rec) (counts : Array Nat)
    (waiting : Std.ExtTreeMap Digest (List Nat) compare) (out : Array Rec) (ready : List Nat) :
    ∀ x ∈ orderLoop rs counts waiting out ready, x ∈ out ∨ x ∈ rs := by
  fun_induction orderLoop rs counts waiting out ready with
  | case1 => exact fun x hx => .inl hx
  | case2 _ _ _ _ _ _ ih => exact ih
  | case3 counts waiting out i ready r hr _ _ _ _ _ ih
  | case4 counts waiting out i ready r hr _ _ ih =>
    intro x hx
    rcases ih x hx with h | h
    · rcases Array.mem_push.mp h with h | rfl
      · exact .inl h
      · exact .inr (Array.mem_of_getElem? hr)
    · exact .inr h

/-- The order `acceptAll` tries first. -/
def acceptOrderGuess (c : RelStore) (rs : Array Rec) : Array Rec :=
  let (counts, waiting, ready) := planRel c rs
  orderLoop rs counts waiting #[] ready

/-- Every record of the guessed order is a record of the batch. -/
theorem mem_acceptOrderGuess {c : RelStore} {rs : Array Rec} {x : Rec}
    (h : x ∈ acceptOrderGuess c rs) : x ∈ rs := by
  unfold acceptOrderGuess at h
  rcases orderLoop_sub _ _ _ _ _ x h with h | h
  · simp at h
  · exact h

/-- Accept a batch of records, in any order that lets their links resolve, relative to the
boundary. Every record goes through `accept`. Returns the new store and the records that were not
accepted. -/
def acceptAll (c : RelStore) (rs : Array Rec) : RelStore × Array Rec :=
  retry ((acceptOrderGuess c rs).toList.foldl (fun c r => (c.accept r).2) c) rs

/-- **What `acceptAll` guarantees, relative to the boundary.** The chat and the boundary are the
same; every record of `c` is kept; every stored record comes from `c` or from the batch; every
record of the batch that is not left over is stored under its digest; every left-over record is
from the batch. -/
theorem acceptAll_sound (c : RelStore) (rs : Array Rec) :
    (c.acceptAll rs).1.group = c.group ∧ (c.acceptAll rs).1.boundary = c.boundary ∧
    (∀ (k : Digest) (x : Rec), c.raw.map[k]? = some x → (c.acceptAll rs).1.raw.map[k]? = some x) ∧
    (∀ (k : Digest) (x : Rec), (c.acceptAll rs).1.raw.map[k]? = some x →
      c.raw.map[k]? = some x ∨ x ∈ rs) ∧
    (∀ x ∈ rs, x ∉ (c.acceptAll rs).2 → (c.acceptAll rs).1.raw.map[hashRecord x]? = some x) ∧
    (∀ x ∈ (c.acceptAll rs).2, x ∈ rs) := by
  obtain ⟨hg, hb, hk, ho⟩ := fold_accept (acceptOrderGuess c rs).toList c
  have h := (retry_spec ((acceptOrderGuess c rs).toList.foldl (fun c r => (c.accept r).2) c) rs).1
  unfold acceptAll
  refine ⟨h.group_eq.trans hg, h.boundary_eq.trans hb, fun k x hx => h.keeps k x (hk k x hx),
    fun k x hx => ?_, fun x hx hl => h.stored x (by simpa using hx) (by simpa using hl),
    fun x hx => by simpa using h.left_sub x (by simpa using hx)⟩
  rcases h.only k x hx with h' | h'
  · rcases ho k x h' with h'' | h''
    · exact .inl h''
    · exact .inr (mem_acceptOrderGuess (by simpa using h''))
  · exact .inr (by simpa using h')

/-- **Nothing left over could still be accepted:** `accept` refuses every left-over record in the
final store. -/
theorem acceptAll_stuck (c : RelStore) (rs : Array Rec) :
    ∀ x ∈ (c.acceptAll rs).2, ∀ d, ((c.acceptAll rs).1.accept x).1 ≠ .accepted d :=
  (retry_spec _ rs).2

/-- After `acceptAll`, `accept` says `accepted` for a record of the batch only if it is stored:
what `ACCEPT_VIEW` replies for each record is what `accept` says in the final store. -/
theorem acceptAll_accepted {c : RelStore} {rs : Array Rec} {x : Rec} {d : Digest} (hx : x ∈ rs)
    (h : ((c.acceptAll rs).1.accept x).1 = .accepted d) :
    d = hashRecord x ∧ (c.acceptAll rs).1.raw.map[d]? = some x := by
  have hraw : rawAcceptRel (c.acceptAll rs).1.raw (c.acceptAll rs).1.boundary x =
      (.accepted d, ((c.acceptAll rs).1.accept x).2.raw) := Prod.ext h rfl
  obtain ⟨rfl, -⟩ := rawAcceptRel_accepted hraw
  refine ⟨rfl, ?_⟩
  by_cases hl : x ∈ (c.acceptAll rs).2
  · exact absurd h (acceptAll_stuck c rs x hl _)
  · exact (acceptAll_sound c rs).2.2.2.2.1 x hx hl

/-! ## Loading, salvaging and merging -/

/-- The smallest digest at which two different records meet: a given record and a stored one,
or two given records. `none` if there is no such digest. -/
def findCollision (c : RelStore) (left : Array (Digest × Rec)) : Option Digest :=
  let (_, found) := left.foldl (init := ((∅ : RecMap), (∅ : DigestSet))) fun (seen, found) (d, r) =>
    match (c.get d).orElse fun _ => seen[d]? with
    | some other => if other = r then (seen, found) else (seen, found.insert d)
    | none => (seen.insert d r, found)
  found.min?

/-- For records that were not accepted: their digests, and the digests their links point to that
are neither stored, nor boundary digests, nor one of these records. Both sorted. -/
def leftoverReport (c : RelStore) (left : Array (Digest × Rec)) : Array Digest × Array Digest :=
  let dropped : DigestSet := left.foldl (fun s (d, _) => s.insert d) ∅
  let missing : DigestSet := left.foldl (init := ∅) fun s (_, r) =>
    r.links.foldl (init := s) fun s l =>
      if c.has l || c.boundary.contains l || dropped.contains l then s else s.insert l
  (dropped.toList.toArray, missing.toList.toArray)

/-- Why `acceptAll` left records over, as an error reply: a collision if there is one, then a full
store, otherwise the records that cannot be accepted and the digests they lack. -/
def explain (c : RelStore) (left : Array Rec) : OpenError :=
  let left := CheckedStore.withDigests left
  match c.findCollision left with
  | some d => .collision d
  | none =>
    if maxRecords ≤ c.size + 1 then .tooLarge
    else
      let (records, missing) := c.leftoverReport left
      .unverifiable records missing

/-- Load the records `u` as a new store of chat `g` over the boundary `B` (a relative store's
blob, `OPEN`). Every record must be accepted; otherwise nothing is loaded and the error says
why. -/
def load (g : GroupId) (B : Boundary) (u : Array Rec) : Except OpenError RelStore :=
  if hB : B.size < maxRecords then
    match CheckedStore.checkInput g u with
    | some e => .error e
    | none =>
      let (c, left) := (emptyWith g B hB).acceptAll u
      if left.isEmpty then .ok c else .error (c.explain left)
  else .error .tooLarge

/-- A successful `load` holds exactly the given records, each under its digest, over exactly the
given boundary; the input was within the size limits and all of chat `g`. -/
theorem load_ok {g : GroupId} {B : Boundary} {u : Array Rec} {c : RelStore}
    (h : load g B u = .ok c) :
    c.group = g ∧ c.boundary = B ∧ WellSized u ∧ (∀ r ∈ u, r.group = g) ∧
      ∀ (k : Digest) (x : Rec), c.raw.map[k]? = some x ↔ x ∈ u ∧ hashRecord x = k := by
  unfold load at h
  split at h
  · rename_i hB
    split at h
    · simp at h
    rename_i hcheck
    have hws : WellSized u := by
      unfold CheckedStore.checkInput at hcheck
      by_cases hw : WellSized u
      · exact hw
      · simp [hw] at hcheck
    have hchat : ∀ r ∈ u, r.group = g := by
      unfold CheckedStore.checkInput at hcheck
      simp only [hws, ↓reduceIte] at hcheck
      intro r hr
      split at hcheck
      · rename_i hall
        simp only [CheckedStore.allInChat, Array.all_eq_true_iff_forall_mem, beq_iff_eq] at hall
        exact hall r hr
      · simp at hcheck
    obtain ⟨hg, hb, _, honly, hall, _⟩ := acceptAll_sound (emptyWith g B hB) u
    generalize (emptyWith g B hB).acceptAll u = res at h hg hb honly hall
    obtain ⟨e, left⟩ := res
    dsimp only at h hg hb honly hall
    split at h
    · rename_i hleft
      simp only [Except.ok.injEq] at h
      subst c
      have hnil : ∀ x, x ∉ left := by
        intro x hx; simp_all [Array.isEmpty_iff]
      refine ⟨hg, hb, hws, hchat, fun k x => ⟨fun hk => ?_, ?_⟩⟩
      · rcases honly k x hk with he | hu
        · simp [emptyWith] at he
        · exact ⟨hu, e.built.hash_eq k x hk⟩
      · rintro ⟨hu, rfl⟩
        exact hall x hu (hnil x)
    · simp at h
  · simp at h

/-- **Completeness of `load`.** Records within the size limits, all of chat `g`, with no two
different records sharing a digest, and that can be listed in an accept order relative to `B`,
are all loaded over a boundary under its size limit. -/
theorem load_complete {g : GroupId} {B : Boundary} {u : Array Rec} (hB : B.size < maxRecords)
    (hw : WellSized u) (hg : ∀ r ∈ u, r.group = g)
    (hcol : ∀ x ∈ u, ∀ y ∈ u, hashRecord x = hashRecord y → x = y)
    (hord : ∃ l, AcceptOrderRel B l ∧ ∀ r, r ∈ l ↔ r ∈ u) :
    ∃ c, load g B u = .ok c := by
  have hchat : CheckedStore.allInChat g u = true := by
    simp only [CheckedStore.allInChat, Array.all_eq_true_iff_forall_mem, beq_iff_eq]
    exact hg
  have hcheck : CheckedStore.checkInput g u = none := by
    simp [CheckedStore.checkInput, hw, hchat]
  unfold load
  simp only [hB, ↓reduceDIte, hcheck]
  obtain ⟨hgrp, hbnd, _, honly, hstored, hleftsub⟩ := acceptAll_sound (emptyWith g B hB) u
  have hstuck := acceptAll_stuck (emptyWith g B hB) u
  generalize (emptyWith g B hB).acceptAll u = res at hgrp hbnd honly hstored hleftsub hstuck ⊢
  obtain ⟨e, left⟩ := res
  dsimp only at hgrp hbnd honly hstored hleftsub hstuck ⊢
  have honly' : ∀ k x, e.raw.map[k]? = some x → x ∈ u := fun k x hk =>
    (honly k x hk).resolve_left (by simp [emptyWith])
  have hegrp : e.raw.group = g := hgrp
  have hebnd : e.boundary = B := hbnd
  -- `accept` takes any record of `u` whose links are all stored or boundary digests.
  have hok : ∀ x ∈ u, (∀ d ∈ x.links, d ∈ e.raw.map ∨ d ∈ B) →
      (rawAcceptRel e.raw e.boundary x).1 = .accepted (hashRecord x) := by
    intro x hx hl
    apply rawAcceptRel_of_ok ((hg x hx).trans hegrp.symm) (hw.2 x hx) (hebnd ▸ hl)
    · intro old hold
      exact hcol old (honly' _ _ hold) x hx (e.built.hash_eq _ _ hold)
    · intro hn
      have := CheckedStore.size_lt_of_keys (m := e.raw.map) (u := u) (r := x) (fun k hk => by
        obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp
          (Std.ExtTreeMap.mem_iff_isSome_getElem?.mp hk)
        exact ⟨y, honly' k y hy, e.built.hash_eq k y hy⟩) hx hn
      have := hw.1
      omega
  -- So every record of `u` is stored: by the accept order.
  obtain ⟨l, hl, hmem⟩ := hord
  have hall : ∀ x ∈ l, e.raw.map[hashRecord x]? = some x := by
    apply hl.all_stored
    intro x hx hlinks
    have hxu := (hmem x).mp hx
    by_cases hxl : x ∈ left
    · exact absurd (by rw [accept_fst]; exact hok x hxu hlinks) (hstuck x hxl (hashRecord x))
    · exact hstored x hxu hxl
  -- And nothing is left over.
  have hleft : left = #[] := by
    rw [Array.eq_empty_iff_forall_not_mem]
    intro x hx
    have hxu := hleftsub x hx
    have hs := hall x ((hmem x).mpr hxu)
    exact hstuck x hx (hashRecord x) (by
      rw [accept_fst]
      exact hok x hxu (fun d hd => hebnd ▸ e.built.closed _ x hs d hd))
  simp [hleft]

/-- **A relative store reloads as itself:** loading its own records over its own boundary, under
its own chat, gives back exactly that store (heads included). -/
theorem load_reopens (c : RelStore) : load c.group c.boundary c.records = .ok c := by
  have hmemr : ∀ x, x ∈ c.records ↔ ∃ k : Digest, c.raw.map[k]? = some x := fun _ => mem_records
  have hws : WellSized c.records := by
    refine ⟨?_, fun r hr => ?_⟩
    · simp only [records, List.size_toArray, List.length_map, Std.ExtTreeMap.length_toList]
      exact c.built.size_lt
    · obtain ⟨k, hk⟩ := (hmemr r).mp hr
      exact c.built.wellSized k r hk
  have hkey : ∀ k x, c.raw.map[k]? = some x ↔ x ∈ c.records ∧ hashRecord x = k := by
    intro k x
    constructor
    · intro hk
      exact ⟨(hmemr x).mpr ⟨k, hk⟩, c.built.hash_eq k x hk⟩
    · rintro ⟨hx, rfl⟩
      obtain ⟨k', hk'⟩ := (hmemr x).mp hx
      rwa [c.built.hash_eq k' x hk']
  obtain ⟨e, he⟩ := load_complete c.built.boundary_lt hws
    (fun r hr => by obtain ⟨k, hk⟩ := (hmemr r).mp hr; exact c.built.group_eq k r hk)
    (fun x hx y hy hxy => by
      obtain ⟨kx, hkx⟩ := (hmemr x).mp hx
      obtain ⟨ky, hky⟩ := (hmemr y).mp hy
      rw [c.built.hash_eq kx x hkx, c.built.hash_eq ky y hky] at hxy
      subst hxy
      rw [hkx] at hky
      exact Option.some.inj hky)
    (by
      obtain ⟨l, hl, hmem⟩ := c.built.order
      exact ⟨l, hl, fun r => (hmem r).trans (hmemr r).symm⟩)
  change load c.raw.group c.boundary c.records = .ok c
  rw [he]
  obtain ⟨hgrp, hbnd, _, _, hemap⟩ := load_ok he
  have hmap : e.raw.map = c.raw.map := by
    apply Std.ExtTreeMap.ext_getElem?
    intro k
    apply Option.ext
    intro x
    rw [hemap k x, hkey k x]
  have hheads : e.raw.heads = c.raw.heads := by
    apply Std.ExtTreeSet.ext_mem
    intro d
    rw [e.built.heads_iff, c.built.heads_iff, hmap, hbnd]
  congr 1
  apply ext _ hbnd
  have hg' : e.raw.group = c.raw.group := hgrp
  cases he' : e.raw
  cases hc' : c.raw
  rw [he', hc'] at hg' hmap hheads
  simp only at hg' hmap hheads
  rw [hg', hmap, hheads]

/-- The result of `salvage`: the store of the records that were accepted, the digests of the
records that were dropped, and the digests the dropped records link that point to nothing. -/
structure Salvaged where
  /-- The accepted records, over the boundary. -/
  store : RelStore
  /-- The digests of the records that were not accepted, sorted. -/
  dropped : Array Digest
  /-- The link digests of the dropped records that point to no record and no boundary digest,
  sorted. -/
  missing : Array Digest

/-- Load as many of the records `u` as can be accepted, as a new store of chat `g` over the
boundary `B`, and name the rest. It refuses (loads nothing) if the input or the boundary is too
large, holds a record of another chat, or holds two different records with the same digest. -/
def salvage (g : GroupId) (B : Boundary) (u : Array Rec) : Except OpenError Salvaged :=
  if hB : B.size < maxRecords then
    match CheckedStore.checkInput g u with
    | some e => .error e
    | none =>
      let (c, left) := (emptyWith g B hB).acceptAll u
      let left := CheckedStore.withDigests left
      match c.findCollision left with
      | some d => .error (.collision d)
      | none =>
        let (dropped, missing) := c.leftoverReport left
        .ok ⟨c, dropped, missing⟩
  else .error .tooLarge

/-- `addBoundaryAll` keeps the chat and the records, and every boundary digest. -/
theorem addBoundaryAll_spec {c e : RelStore} {es : List (Digest × Aci)}
    (h : c.addBoundaryAll es = some e) :
    e.raw.group = c.raw.group ∧ e.raw.map = c.raw.map ∧ ∀ d ∈ c.boundary, d ∈ e.boundary := by
  induction es generalizing c with
  | nil =>
    simp only [addBoundaryAll, Option.some.injEq] at h
    subst h
    exact ⟨rfl, rfl, fun _ h => h⟩
  | cons p rest ih =>
    obtain ⟨d, v⟩ := p
    simp only [addBoundaryAll, Option.bind_eq_some_iff] at h
    obtain ⟨c', h1, h2⟩ := h
    obtain ⟨hg, hm, -, hkeep, -⟩ := addBoundary_spec h1
    obtain ⟨hg', hm', hb'⟩ := ih h2
    refine ⟨hg'.trans hg, hm'.trans hm, fun x hx => hb' x ?_⟩
    obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp (Std.ExtTreeMap.mem_iff_isSome_getElem?.mp hx)
    exact Std.ExtTreeMap.mem_iff_isSome_getElem?.mpr (by simp [hkeep x a ha])

/-- Add every record and boundary digest of `d` to the relative store `c` (`MERGE`). Succeeds only
if every record is accepted; on an error the caller keeps `c` unchanged. -/
def merge (c d : RelStore) : Except OpenError RelStore :=
  if d.group ≠ c.group then .error .wrongChat
  else
    match c.addBoundaryAll d.boundary.toList with
    | none => .error .tooLarge
    | some c' =>
      let (e, left) := c'.acceptAll d.records
      if left.isEmpty then .ok e else .error (e.explain left)

/-- A successful merge holds exactly the records of both stores, keeps `c`'s chat, and keeps every
boundary digest of `c`. -/
theorem merge_ok {c d e : RelStore} (h : c.merge d = .ok e) :
    e.group = c.group ∧ (∀ x ∈ c.boundary, x ∈ e.boundary) ∧ ∀ (k : Digest) (x : Rec),
      e.raw.map[k]? = some x ↔ c.raw.map[k]? = some x ∨ d.raw.map[k]? = some x := by
  unfold merge at h
  split at h
  · simp at h
  split at h
  · simp at h
  rename_i c' hadd
  obtain ⟨hg0, hm0, hb0⟩ := addBoundaryAll_spec hadd
  obtain ⟨hg, hb, hkeep, honly, hall, _⟩ := acceptAll_sound c' d.records
  generalize c'.acceptAll d.records = res at h hg hb hkeep honly hall
  obtain ⟨e', left⟩ := res
  dsimp only at h hg hb hkeep honly hall
  split at h
  · rename_i hleft
    simp only [Except.ok.injEq] at h
    subst e
    have hnil : ∀ x, x ∉ left := by
      intro x hx; simp_all [Array.isEmpty_iff]
    refine ⟨hg.trans hg0, fun x hx => hb ▸ hb0 x hx, fun k x => ⟨fun hk => ?_, ?_⟩⟩
    · rcases honly k x hk with hc | hd
      · exact Or.inl (hm0 ▸ hc)
      · obtain ⟨k', hk'⟩ := mem_records.mp hd
        have h1 := d.built.hash_eq k' x hk'
        have h2 := e'.built.hash_eq k x hk
        exact Or.inr (by rw [← h2, h1]; exact hk')
    · rintro (hc | hd)
      · exact hkeep k x (hm0 ▸ hc)
      · have := hall x (mem_records.mpr ⟨k, hd⟩) (hnil x)
        rwa [d.built.hash_eq k x hd] at this
  · simp at h

end RelStore

/-! ## Example: a newcomer's store

Bob joins after `a1`. His catch-up gives him `a1` as a boundary digest (vouched by Alice) and
the records `b1`, `c1` and `a2`, which link it. Later a reply carries the record `a1` itself
(promotion). -/

namespace Examples

open RelStore

/-- Alice vouches for `a1`'s digest. -/
def bnd : Boundary := (∅ : Boundary).insert (hashRecord a1) alice

/-- Bob's store after his catch-up. -/
def relStore : RelStore := ((emptyWith group bnd (by decide)).acceptAll #[a2, c1, b1]).1

/-- The same, with `a1`'s record promoted. -/
def relPromoted : RelStore := (relStore.accept a1).2

end Examples

open Examples RelStore

-- `headOnArrival`: `b1` is a head when it arrives (nothing links it). Once `b1` links the boundary
-- digest of `a1`, `a1`'s record would not be a head on arrival.
#guard headOnArrival (emptyWith group bnd (by decide)).heads bnd b1 (hashRecord b1)
#guard !headOnArrival relStore.heads bnd a1 (hashRecord a1)
-- The order `acceptAll` tries first puts `a2` after the replies it links.
#guard (acceptOrderGuess (emptyWith group bnd (by decide)) #[a2, c1, b1]).toList.getLast? ==
  some a2
-- `addBoundaryAll`: a digest given twice keeps its first voucher; it becomes a head.
#guard match (RelStore.empty group).addBoundaryAll [(hashRecord a1, alice), (hashRecord a1, bob)]
    with
  | some c => c.boundary.toList == [(hashRecord a1, alice)] && c.headsArray == #[hashRecord a1]
  | none => false
-- Before any record, the boundary digest is the only head.
#guard (emptyWith group bnd (by decide)).headsArray == #[hashRecord a1]
-- `b1`, `c1` and `a2` are accepted over the boundary; the heads are those of the closed store.
#guard ((emptyWith group bnd (by decide)).acceptAll #[a2, c1, b1]).2.size == 0
#guard relStore.headsArray == all4.headsArray
#guard relStore.size == 3 && !relStore.has (hashRecord a1)
#guard relStore.boundaryDigests.toList == [hashRecord a1]
-- A closed store refuses the same records: `a1` is missing.
#guard ((CheckedStore.empty group).acceptAll #[a2, c1, b1]).2.size == 3
-- `accept` says what is missing beyond the boundary: here nothing, then a digest it lacks.
#guard (relStore.accept b1).1 == .accepted (hashRecord b1)
#guard match ((emptyWith group bnd (by decide)).accept a2).1 with
  | .missing ds => ds.size == 2 && ds.contains (hashRecord b1) && ds.contains (hashRecord c1)
  | _ => false
-- Promotion: `a1` arrives as a record; it is stored, no longer a boundary digest, and the heads
-- do not change. Its digest stays in `boundary`, the record of what was vouched.
#guard (relStore.accept a1).1 == .accepted (hashRecord a1)
#guard relPromoted.has (hashRecord a1) && relPromoted.boundaryDigests.toList == [] &&
  relPromoted.headsArray == relStore.headsArray && relPromoted.boundary.size == 1
-- `LINKABLE`: `a2` is a head and a stored record; it is linkable only when the host holds it live.
#guard relStore.linkable ((∅ : DigestSet).insert (hashRecord a2)) == #[hashRecord a2]
#guard relStore.linkable ∅ == #[]
-- A store whose only head is a boundary digest links nothing.
#guard (emptyWith group bnd (by decide)).linkable ((∅ : DigestSet).insert (hashRecord a1)) == #[]
-- `load` reloads both stores from their records and boundary.
#guard match load group bnd relStore.records with
  | .ok c => c.headsArray == relStore.headsArray && c.size == 3
  | .error _ => false
#guard match load group bnd relPromoted.records with
  | .ok c => c.headsArray == relPromoted.headsArray && c.size == 4
  | .error _ => false
-- Without the boundary, the records do not load: `a1` is missing.
#guard match load group ∅ relStore.records with
  | .error (.unverifiable _ m) => m == #[hashRecord a1]
  | _ => false
-- `salvage` keeps what checks; `merge` adds a closed store's records.
#guard match salvage group ∅ relStore.records with
  | .ok sv => sv.store.size == 0 && sv.missing == #[hashRecord a1]
  | .error _ => false
#guard match relStore.merge (ofChecked storeAB) with
  | .ok e => e.size == 4 && e.boundaryDigests.toList == []
  | .error _ => false

-- The guarantees, on concrete inputs.
example : load relStore.group relStore.boundary relStore.records = .ok relStore :=
  load_reopens relStore
example : ∃ c, load group bnd #[b1] = .ok c :=
  load_complete (by decide) (by decide) (by simp [b1])
    (by simp) ⟨[b1], .cons (by simp [b1, bnd]) .nil, by simp⟩
example : (rawAcceptRel (emptyWith group bnd (by decide)).raw bnd b1).1 =
    .accepted (hashRecord b1) :=
  rawAcceptRel_of_ok rfl (by decide) (by simp [b1, bnd]) (by simp [emptyWith])
    (fun _ => by simp [emptyWith, maxRecords])
example : BuiltRel (CheckedStore.empty group).raw ∅ := builtRel_empty_iff.mpr
  (CheckedStore.empty group).built

-- `BuiltRel` rejects bad stores: a head that is neither stored nor a boundary digest; a boundary
-- digest that a record links but that is listed as a head.
example : ¬ BuiltRel ⟨group, ∅, (∅ : DigestSet).insert (dig 1)⟩ ∅ := fun h => by
  simpa using ((h.heads_iff (dig 1)).mp (by simp)).1
example : ¬ BuiltRel ⟨group, (∅ : RecMap).insert (hashRecord b1) b1,
    ((∅ : DigestSet).insert (hashRecord a1)).insert (hashRecord b1)⟩ bnd := fun h => by
  have := ((h.heads_iff (hashRecord a1)).mp (by simp)).2 (hashRecord b1) b1 (by simp)
  exact this (by simp [b1])
example : ¬ AcceptOrderRel ∅ [b1] := by
  rintro (_ | ⟨h, _⟩)
  rcases h (hashRecord a1) (by simp [b1]) with h | ⟨_, h, _⟩ <;> simp at h

end Zrdt
