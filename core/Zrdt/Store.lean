import Zrdt.Encode
import Std.Data.ExtTreeMap
import Std.Data.ExtTreeSet

/-!
# The checked store (docs/PLAN.md §3.3, phase B)

A chat's store holds every record the app accepted, keyed by digest, and the store's heads (the
records nothing links yet).

- `RawStore` is the data: the chat id, the map from digest to record, and the heads.
- `Built c` says the data is right. Every key is its record's digest; every record belongs to
  the chat; the heads are exactly the keys no record links; the records can be listed in an order
  in which each one's links were already present when it was added (`AcceptOrder`); and the size
  limits of §3.4 hold.
- `CheckedStore` is a `RawStore` together with a proof of `Built`. There is no other way to make
  one: `empty` and `accept` are the only constructors, and `acceptAll`, `merge`, `open` and
  `salvage` add records only through `accept`. The proof is erased, so the compiled code is the
  same as without it.

**`accept`** adds one record if its links are all present. Otherwise the store is unchanged and
the result says why: `missing` (the links that are not present, sorted), `collision` (a different
record with the same digest is stored), `wrongChat` or `tooLarge`. Adding a record that is already
stored is `accepted` and changes nothing.

**`acceptAll`** adds a batch of records in whatever order lets their links resolve (Kahn's
algorithm, then one more pass over what is left). It returns the records it could not add. `open`
(load a saved store), `salvage` (load the part that checks) and `merge` (add another store) are
built on it.

**Observers:** `heads`, `has`, `get`, `reachSet` (the records reached by following links) and
`encode` (the store blob, records sorted by digest).

The maps are `Std.ExtTreeMap` and `Std.ExtTreeSet`: two maps with the same contents are equal
(`=`), whatever order the records were added in.

**Proved here** (no Mathlib; the statements about the spec model are in `Crdt`):

- `rawAccept_built`: `accept` keeps a store correct.
- `rawAccept_accepted`, `rawAccept_missing`, `rawAccept_collision`, `rawAccept_wrongChat`,
  `rawAccept_tooLarge`: what each result means; any result but `accepted` leaves the store as it
  was. `rawAccept_of_ok`: a record that passes every check is accepted.
- `acceptAll_sound`: `acceptAll` keeps every stored record and adds only records of the batch;
  every batch record not left over is stored. `acceptAll_stuck`: `accept` refuses every left-over
  record in the final store.
- `merge_ok`: a successful merge holds exactly the records of both stores. `openRecords_ok` and
  `openRecords_complete`: `open` loads exactly the given records, and it succeeds whenever they
  are within the limits, all of the chat, never two under one digest, and in some accept order.
- `encode_reopens`: opening a store's blob gives back exactly that store.
-/

namespace Zrdt

/-- A digest map: digest to record. -/
abbrev RecMap := Std.ExtTreeMap Digest Rec compare

/-- A set of digests, kept sorted. -/
abbrev DigestSet := Std.ExtTreeSet Digest compare

/-! ## The raw store -/

/-- A chat's records and heads, with no checks. Only `CheckedStore` (below) is used by the app;
this is public so that proofs and the daemon can read the fields. -/
structure RawStore where
  /-- The chat every record must belong to. -/
  group : GroupId
  /-- Every record, keyed by its digest. -/
  map : RecMap
  /-- The digests of the records that no record links (the newest ones). -/
  heads : DigestSet

/-- `AcceptOrder l`: the list is newest first, and every record's links are digests of records
further down the list (older ones). So adding the records from the end of the list to the front,
each one's links are present when it is added. -/
inductive AcceptOrder : List Rec → Prop
  /-- The empty list. -/
  | nil : AcceptOrder []
  /-- A record whose links are all digests of older records, on top of an accept order. -/
  | cons {r : Rec} {older : List Rec} :
      (∀ d ∈ r.links, ∃ r' ∈ older, hashRecord r' = d) → AcceptOrder older →
      AcceptOrder (r :: older)

/-- Every record reached through an accept order is stored, if each record of the order whose
links are stored is itself stored. -/
theorem AcceptOrder.all_stored {m : RecMap} {l : List Rec} (hl : AcceptOrder l)
    (hstep : ∀ x ∈ l, (∀ d ∈ x.links, d ∈ m) → m[hashRecord x]? = some x) :
    ∀ x ∈ l, m[hashRecord x]? = some x := by
  induction hl with
  | nil => simp
  | @cons r older hr _ ih =>
    have ih' := ih (fun x hx => hstep x (List.mem_cons_of_mem _ hx))
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · apply hstep x List.mem_cons_self
      intro d hd
      obtain ⟨r', hr', rfl⟩ := hr d hd
      exact Std.ExtTreeMap.mem_iff_isSome_getElem?.mpr (by simp [ih' r' hr'])
    · exact ih' x hx

/-- What makes a raw store correct. -/
structure Built (c : RawStore) : Prop where
  /-- Every record is stored under its own digest. -/
  hash_eq : ∀ (k : Digest) (r : Rec), c.map[k]? = some r → hashRecord r = k
  /-- Every record belongs to the store's chat. -/
  group_eq : ∀ (k : Digest) (r : Rec), c.map[k]? = some r → r.group = c.group
  /-- The heads are exactly the stored digests that no stored record links. -/
  heads_iff : ∀ d, d ∈ c.heads ↔
    d ∈ c.map ∧ ∀ (k : Digest) (r : Rec), c.map[k]? = some r → d ∉ r.links
  /-- The records can be listed in an accept order (newest first), and that list holds exactly
  the stored records. -/
  order : ∃ l, AcceptOrder l ∧ ∀ r, r ∈ l ↔ ∃ k : Digest, c.map[k]? = some r
  /-- The store holds fewer than `maxRecords` records. -/
  size_lt : c.map.size < maxRecords
  /-- Every record has at most `maxLinks` links. -/
  wellSized : ∀ (k : Digest) (r : Rec), c.map[k]? = some r → r.WellSized

/-- Every link of an accept order is the digest of a record in it. -/
theorem AcceptOrder.links {l : List Rec} (h : AcceptOrder l) :
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

/-- In a correct store, every link of every record is a stored digest (nothing is missing). -/
theorem Built.closed {c : RawStore} (h : Built c) :
    ∀ (k : Digest) (r : Rec), c.map[k]? = some r → ∀ d ∈ r.links, d ∈ c.map := by
  intro k r hk d hd
  obtain ⟨l, hl, hmem⟩ := h.order
  obtain ⟨r', hr', he⟩ := hl.links r ((hmem r).mpr ⟨k, hk⟩) d hd
  obtain ⟨k', hk'⟩ := (hmem r').mp hr'
  have := h.hash_eq k' r' hk'
  subst he; subst this
  exact Std.ExtTreeMap.mem_iff_isSome_getElem?.mpr (by simp [hk'])

/-! ## Accepting one record -/

/-- What `accept` did with a record. -/
inductive AcceptResult
  /-- Added (or already stored, the same record); `d` is its digest. -/
  | accepted (d : Digest)
  /-- Not added: these links are not stored (sorted, never empty). -/
  | missing (ds : Array Digest)
  /-- Not added: a different record with digest `d` is stored. -/
  | collision (d : Digest)
  /-- Not added: the record belongs to another chat. -/
  | wrongChat
  /-- Not added: the record has too many links, or the store is full. -/
  | tooLarge
deriving DecidableEq, Repr

/-- Remove the given digests from a set of heads. -/
def dropLinks (hs : DigestSet) (ls : Array Digest) : DigestSet :=
  ls.foldl (fun s l => s.erase l) hs

open Examples in
#guard (dropLinks ((∅ : DigestSet).insert (dig 1) |>.insert (dig 2)) #[dig 1, dig 3]).toList ==
  [dig 2]

/-- `d` survives `dropLinks` exactly when it was a head and is not one of the links. -/
theorem mem_dropLinks {hs : DigestSet} {ls : Array Digest} {d : Digest} :
    d ∈ dropLinks hs ls ↔ d ∈ hs ∧ d ∉ ls := by
  unfold dropLinks
  rw [← Array.foldl_toList]
  simp only [← Array.mem_toList_iff]
  induction ls.toList generalizing hs with
  | nil => simp
  | cons l rest ih =>
    simp only [List.foldl_cons, ih, Std.ExtTreeSet.mem_erase, ne_eq,
      Std.LawfulEqCmp.compare_eq_iff_eq, List.mem_cons, not_or]
    constructor
    · rintro ⟨⟨hne, hd⟩, hr⟩; exact ⟨hd, fun h => hne h.symm, hr⟩
    · rintro ⟨hd, hne, hr⟩; exact ⟨⟨fun h => hne h.symm, hd⟩, hr⟩

/-- The links of `r` that the map does not hold, in order. -/
def missingLinks (m : RecMap) (r : Rec) : Array Digest :=
  r.links.filter (fun l => !m.contains l)

/-- A link is missing exactly when it is a link of `r` and not a key of the map. -/
theorem mem_missingLinks {m : RecMap} {r : Rec} {d : Digest} :
    d ∈ missingLinks m r ↔ d ∈ r.links ∧ d ∉ m := by
  rw [missingLinks, Array.mem_filter, Std.ExtTreeMap.mem_iff_contains]
  cases m.contains d <;> simp

/-- The missing links are sorted, like the links. -/
theorem missingLinks_sorted {m : RecMap} {r : Rec} : StrictlySorted (missingLinks m r) := by
  unfold StrictlySorted missingLinks
  rw [Array.toList_filter]
  exact r.links_sorted.filter _

/-- Accept one record into a raw store (see the module header). The checks, in order: the chat;
the number of links; whether the digest is already stored (the same record: accepted, nothing
changes; a different one: collision); whether the store is full; whether every link is stored.
-/
def rawAccept (c : RawStore) (r : Rec) : AcceptResult × RawStore :=
  if r.group ≠ c.group then (.wrongChat, c)
  else if ¬ r.WellSized then (.tooLarge, c)
  else
    let d := hashRecord r
    match c.map[d]? with
    | some old => if old = r then (.accepted d, c) else (.collision d, c)
    | none =>
      if maxRecords ≤ c.map.size + 1 then (.tooLarge, c)
      else
        let missing := missingLinks c.map r
        if missing.isEmpty then
          (.accepted d, { c with map := c.map.insert d r,
                                 heads := (dropLinks c.heads r.links).insert d })
        else (.missing missing, c)

/-- Accepting keeps a raw store correct. -/
theorem rawAccept_built {c : RawStore} (h : Built c) (r : Rec) : Built (rawAccept c r).2 := by
  unfold rawAccept
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
      have hres : ∀ x ∈ r.links, x ∈ c.map := by
        intro x hx
        refine Classical.byContradiction fun hx' => ?_
        have : x ∈ missingLinks c.map r := mem_missingLinks.mpr ⟨hx, hx'⟩
        simp_all [Array.isEmpty_iff]
      have hcl := h.closed
      have hdnot : hashRecord r ∉ c.map := by
        simp [Std.ExtTreeMap.mem_iff_isSome_getElem?, hnone]
      simp only at *
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
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
      · intro d
        simp only [Std.ExtTreeSet.mem_insert, mem_dropLinks, Std.ExtTreeMap.mem_insert,
          Std.ExtTreeMap.getElem?_insert, Std.LawfulEqCmp.compare_eq_iff_eq]
        constructor
        · rintro (rfl | ⟨hd, hnl⟩)
          · refine ⟨Or.inl rfl, fun k x hk => ?_⟩
            split at hk
            · cases hk; exact fun hl => hdnot (hres _ hl)
            · exact fun hl => hdnot (hcl k x hk _ hl)
          · have := (h.heads_iff d).mp hd
            refine ⟨Or.inr this.1, fun k x hk => ?_⟩
            split at hk
            · cases hk; exact hnl
            · exact this.2 k x hk
        · rintro ⟨hd, hun⟩
          by_cases hdr : hashRecord r = d
          · exact Or.inl hdr
          right
          rcases hd with hd | hd
          · exact absurd hd hdr
          refine ⟨(h.heads_iff d).mpr ⟨hd, fun k x hk => ?_⟩, ?_⟩
          · have hk' : hashRecord r ≠ k := by
              rintro rfl; simp [hnone] at hk
            exact hun k x (by simp [hk', hk])
          · simpa using hun (hashRecord r) r (by simp)
      · obtain ⟨l, hl, hmem⟩ := h.order
        refine ⟨r :: l, .cons (fun d hd => ?_) hl, fun x => ?_⟩
        · have hdm := hres d hd
          obtain ⟨x, hx⟩ : ∃ x, c.map[d]? = some x :=
            Option.isSome_iff_exists.mp (Std.ExtTreeMap.mem_iff_isSome_getElem?.mp hdm)
          exact ⟨x, (hmem x).mpr ⟨d, hx⟩, h.hash_eq d x hx⟩
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

/-! ### What `rawAccept` does, case by case -/

/-- Accepted: `d` is the record's digest, and the record is now stored under it (it may have been
stored already; the map is the same then). -/
theorem rawAccept_accepted {c c' : RawStore} {r : Rec} {d : Digest}
    (h : rawAccept c r = (.accepted d, c')) :
    d = hashRecord r ∧ c'.group = c.group ∧ c'.map = c.map.insert d r ∧
      ∀ old, c.map[d]? = some old → old = r := by
  unfold rawAccept at h
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
theorem rawAccept_unchanged {c : RawStore} {r : Rec} (h : ∀ d, (rawAccept c r).1 ≠ .accepted d) :
    (rawAccept c r).2 = c := by
  unfold rawAccept at h ⊢
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

/-- Missing: the list is exactly the links that are not stored, it is not empty, and it is
sorted. -/
theorem rawAccept_missing {c c' : RawStore} {r : Rec} {ds : Array Digest}
    (h : rawAccept c r = (.missing ds, c')) :
    c' = c ∧ ds ≠ #[] ∧ (∀ x, x ∈ ds ↔ x ∈ r.links ∧ x ∉ c.map) ∧ StrictlySorted ds := by
  have hc : c' = c := by
    have := rawAccept_unchanged (c := c) (r := r) (by simp [h])
    rwa [h] at this
  unfold rawAccept at h
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
      refine ⟨rfl, ?_, fun x => mem_missingLinks, missingLinks_sorted⟩
      intro he
      simp [he] at hne

/-- Collision: `d` is the record's digest, and a different record is stored under it. -/
theorem rawAccept_collision {c c' : RawStore} {r : Rec} {d : Digest}
    (h : rawAccept c r = (.collision d, c')) :
    c' = c ∧ d = hashRecord r ∧ ∃ old, c.map[d]? = some old ∧ old ≠ r := by
  have hc : c' = c := by
    have := rawAccept_unchanged (c := c) (r := r) (by simp [h])
    rwa [h] at this
  unfold rawAccept at h
  dsimp only at h
  split at h
  · simp at h
  split at h
  · simp at h
  split at h
  · rename_i old hold
    split at h
    · simp at h
    · rename_i hne
      obtain ⟨⟨⟩, rfl⟩ := Prod.mk.inj h
      exact ⟨rfl, rfl, old, hold, hne⟩
  · split at h
    · simp at h
    split at h <;> simp at h

/-- Wrong chat: the record's chat is not the store's. -/
theorem rawAccept_wrongChat {c c' : RawStore} {r : Rec} (h : rawAccept c r = (.wrongChat, c')) :
    c' = c ∧ r.group ≠ c.group := by
  have hc : c' = c := by
    have := rawAccept_unchanged (c := c) (r := r) (by simp [h])
    rwa [h] at this
  unfold rawAccept at h
  dsimp only at h
  split at h
  · rename_i hg
    exact ⟨hc, hg⟩
  split at h
  · simp at h
  split at h
  · split at h <;> simp at h
  · split at h
    · simp at h
    split at h <;> simp at h

/-- Too large: the record has too many links, or it is new and the store is full. -/
theorem rawAccept_tooLarge {c c' : RawStore} {r : Rec} (h : rawAccept c r = (.tooLarge, c')) :
    c' = c ∧ (¬ r.WellSized ∨ (hashRecord r ∉ c.map ∧ maxRecords ≤ c.map.size + 1)) := by
  have hc : c' = c := by
    have := rawAccept_unchanged (c := c) (r := r) (by simp [h])
    rwa [h] at this
  unfold rawAccept at h
  dsimp only at h
  split at h
  · simp at h
  split at h
  · rename_i hw
    exact ⟨hc, Or.inl hw⟩
  split at h
  · split at h <;> simp at h
  · rename_i hnone
    split at h
    · rename_i hfull
      refine ⟨hc, Or.inr ⟨?_, hfull⟩⟩
      simp [Std.ExtTreeMap.mem_iff_isSome_getElem?, hnone]
    split at h <;> simp at h

/-- A record of the right chat, with few enough links, whose links are all stored, and whose
digest holds no other record, is accepted, unless it is new and the store is full. -/
theorem rawAccept_of_ok {c : RawStore} {r : Rec} (hg : r.group = c.group) (hw : r.WellSized)
    (hl : ∀ x ∈ r.links, x ∈ c.map) (hc : ∀ old, c.map[hashRecord r]? = some old → old = r)
    (hroom : hashRecord r ∉ c.map → c.map.size + 1 < maxRecords) :
    (rawAccept c r).1 = .accepted (hashRecord r) := by
  unfold rawAccept
  dsimp only
  simp only [hg, ne_eq, not_true_eq_false, ↓reduceIte, hw]
  split
  · rename_i old hold
    simp [hc old hold]
  · rename_i hnone
    have hroom' := hroom (by simp [Std.ExtTreeMap.mem_iff_isSome_getElem?, hnone])
    have hfull : ¬ maxRecords ≤ c.map.size + 1 := by omega
    have hmiss : (missingLinks c.map r).isEmpty = true := by
      rw [Array.isEmpty_iff, Array.eq_empty_iff_forall_not_mem]
      intro x hx
      exact (mem_missingLinks.mp hx).2 (hl x (mem_missingLinks.mp hx).1)
    simp [hfull, hmiss]

/-! ## Walking links -/

/-- Erasing a key that is present makes a map smaller (used to show that `walk` ends). -/
theorem size_erase_lt {β : Type} {m : Std.ExtTreeMap Digest β compare} {d : Digest}
    (h : d ∈ m) : (m.erase d).size < m.size := by
  rw [Std.ExtTreeMap.size_erase]
  simp only [Std.ExtTreeMap.mem_iff_contains.mp h, ↓reduceIte]
  have : m.size ≠ 0 := by
    intro h0
    rw [← Std.ExtTreeMap.eq_empty_iff_size_eq_zero] at h0
    simp [h0] at h
  omega

/-- Visit every key reachable from `todo`, where the keys to visit after key `d` are
`next (left[d])`. `left` holds the keys not visited yet (with their values), and `seen` the
visited ones. A digest that is not a key of `left` (unknown, or already visited) is skipped.
Each step either removes a key from `left` or shortens `todo`, so the walk ends. -/
def walk {β : Type} (next : β → List Digest) (left : Std.ExtTreeMap Digest β compare)
    (seen : DigestSet) : List Digest → DigestSet
  | [] => seen
  | d :: todo =>
    if h : d ∈ left then
      walk next (left.erase d) (seen.insert d) (next (left.get d h) ++ todo)
    else walk next left seen todo
termination_by todo => (left.size, todo.length)
decreasing_by
  · exact Prod.Lex.left _ _ (size_erase_lt h)
  · exact Prod.Lex.right _ (by simp)

open Examples in
-- 1 → 2 → 3, and 4 → 1; walking from 2 visits 2 and 3; 9 is not a key.
#guard (walk id (Std.ExtTreeMap.ofList [(dig 1, [dig 2]), (dig 2, [dig 3]), (dig 3, []),
  (dig 4, [dig 1])] compare) ∅ [dig 2, dig 9]).toList == [dig 2, dig 3]

/-! ## The checked store -/

/-- A store together with the proof that it is correct. The only way to get one is `empty`,
`accept`, or a function built on `accept`. -/
structure CheckedStore where
  /-- The data. -/
  raw : RawStore
  /-- The proof that the data is correct (erased in compiled code). -/
  built : Built raw

namespace CheckedStore

/-- The empty store of chat `g`. -/
def empty (g : GroupId) : CheckedStore where
  raw := ⟨g, ∅, ∅⟩
  built := {
    hash_eq := by simp
    group_eq := by simp
    heads_iff := by simp
    order := ⟨[], .nil, by simp⟩
    size_lt := by simp [maxRecords]
    wellSized := by simp }

/-- Two checked stores with the same data are equal (the proof carries no data). -/
theorem ext {c d : CheckedStore} (h : c.raw = d.raw) : c = d := by
  cases c; cases d; cases h; rfl

/-- Accept one record (see `rawAccept`). Returns what happened and the new store. -/
def accept (c : CheckedStore) (r : Rec) : AcceptResult × CheckedStore :=
  let p := rawAccept c.raw r
  (p.1, ⟨p.2, rawAccept_built c.built r⟩)

/-- `accept` reports what `rawAccept` reports. -/
@[simp] theorem accept_fst (c : CheckedStore) (r : Rec) :
    (c.accept r).1 = (rawAccept c.raw r).1 := rfl

/-- `accept`'s new store holds what `rawAccept`'s does. -/
@[simp] theorem accept_raw (c : CheckedStore) (r : Rec) :
    (c.accept r).2.raw = (rawAccept c.raw r).2 := rfl

/-- Every result other than `accepted` leaves the store as it was. -/
theorem accept_unchanged {c : CheckedStore} {r : Rec}
    (h : ∀ d, (c.accept r).1 ≠ .accepted d) : (c.accept r).2 = c :=
  ext (rawAccept_unchanged h)

/-! ## Observers -/

/-- The chat the store belongs to. -/
def group (c : CheckedStore) : GroupId := c.raw.group

/-- The heads: digests of the stored records that no stored record links. -/
def heads (c : CheckedStore) : DigestSet := c.raw.heads

/-- The heads as a sorted array. -/
def headsArray (c : CheckedStore) : Array Digest := c.heads.toList.toArray

/-- Whether a record with digest `d` is stored. -/
def has (c : CheckedStore) (d : Digest) : Bool := c.raw.map.contains d

/-- The record with digest `d`, if stored. -/
def get (c : CheckedStore) (d : Digest) : Option Rec := c.raw.map[d]?

/-- The number of stored records. -/
def size (c : CheckedStore) : Nat := c.raw.map.size

/-- The stored records, sorted by digest. -/
def records (c : CheckedStore) : Array Rec := (c.raw.map.toList.map Prod.snd).toArray

/-- The records of a store are the values of its map. -/
theorem mem_records {c : CheckedStore} {x : Rec} :
    x ∈ c.records ↔ ∃ k : Digest, c.raw.map[k]? = some x := by
  simp only [records, List.mem_toArray, List.mem_map]
  constructor
  · rintro ⟨⟨k, y⟩, hk, rfl⟩
    exact ⟨k, Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some.mp hk⟩
  · rintro ⟨k, hk⟩
    exact ⟨(k, x), Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some.mpr hk, rfl⟩

/-- The store blob (docs/PLAN.md §3.4): the chat id and the records sorted by digest. The heads
are not written; `open` recomputes them. -/
def encode (c : CheckedStore) : ByteArray := encodeBlob c.group c.records

/-! ## Reachability -/

/-- The stored records reached from the digests `start` by following links, as their digests
(`start` included). A start digest that is not stored is left out. -/
def reachSet (c : CheckedStore) (start : Array Digest) : DigestSet :=
  walk (fun r => r.links.toList) c.raw.map ∅ start.toList

/-! ## Accepting many records -/

/-- For each record: how many of its links the store lacks. For each lacking digest: the
records (by index) that wait for it. And the records that wait for nothing, in input order. -/
def plan (c : CheckedStore) (rs : Array Rec) :
    Array Nat × Std.ExtTreeMap Digest (List Nat) compare × List Nat :=
  let (counts, waiting, ready) := rs.foldl (init := (#[], ∅, [])) fun (counts, waiting, ready) r =>
    let i := counts.size
    let lacking := r.links.filter (fun l => !c.has l)
    (counts.push lacking.size,
     lacking.foldl (fun w l => w.insert l (i :: w.getD l [])) waiting,
     if lacking.isEmpty then i :: ready else ready)
  (counts, waiting, ready.reverse)

/-- Lower the count of each record in `js` by one. Returns the new counts and the records whose
count reached zero. -/
def release (counts : Array Nat) (js : List Nat) : Array Nat × List Nat :=
  js.foldl (init := (counts, [])) fun (counts, freed) j =>
    let counts := counts.modify j (· - 1)
    (counts, if counts[j]? = some 0 then j :: freed else freed)

#guard release #[2, 1, 1] [1, 2, 0] == (#[1, 0, 0], [2, 1])

/-- The worklist loop of `acceptAll`. `ready` holds the records whose links are all stored.
Each is passed to `accept`; when one is added, the records waiting for its digest count down,
and those that reach zero become ready. `done` marks the records that were accepted. -/
def acceptLoop (rs : Array Rec) (c : CheckedStore) (counts : Array Nat)
    (waiting : Std.ExtTreeMap Digest (List Nat) compare) (done : Array Bool) :
    List Nat → CheckedStore × Array Bool
  | [] => (c, done)
  | i :: ready =>
    match rs[i]? with
    | none => acceptLoop rs c counts waiting done ready
    | some r =>
      match c.accept r with
      | (.accepted d, c') =>
        let done := done.setIfInBounds i true
        if h : d ∈ waiting then
          let (counts, freed) := release counts (waiting.get d h)
          acceptLoop rs c' counts (waiting.erase d) done (freed ++ ready)
        else acceptLoop rs c' counts waiting done ready
      | (_, c') => acceptLoop rs c' counts waiting done ready
termination_by ready => (waiting.size, ready.length)
decreasing_by
  all_goals first
    | exact Prod.Lex.right _ (by simp)
    | exact Prod.Lex.left _ _ (size_erase_lt h)

/-- The records not marked done, in order. -/
def leftovers (rs : Array Rec) (done : Array Bool) : Array Rec :=
  (rs.zip done).filterMap fun (r, ok) => if ok then none else some r

/-- Accept a batch of records in an order that lets their links resolve (Kahn's algorithm).
Returns the new store and the records that were not accepted, in input order. -/
def kahn (c : CheckedStore) (rs : Array Rec) : CheckedStore × Array Rec :=
  let (counts, waiting, ready) := plan c rs
  let (c', done) := acceptLoop rs c counts waiting (Array.replicate rs.size false) ready
  (c', leftovers rs done)

/-- Offer each record to `accept` once, in order. Returns the new store and, after `keep`, the
records that were not accepted. -/
def retryPass (c : CheckedStore) (keep : Array Rec) : List Rec → CheckedStore × Array Rec
  | [] => (c, keep)
  | r :: rest =>
    match c.accept r with
    | (.accepted _, c') => retryPass c' keep rest
    | (_, c') => retryPass c' (keep.push r) rest

/-- Offer the records to `accept` again and again, until a pass accepts none of them. Returns
the new store and the records never accepted. -/
def retry (c : CheckedStore) (left : Array Rec) : CheckedStore × Array Rec :=
  let (c', keep) := retryPass c #[] left.toList
  if keep.size < left.size then retry c' keep else (c', keep)
termination_by left.size

/-- Accept a batch of records, in any order that lets their links resolve. Every record goes
through `accept`. Returns the new store and the records that were not accepted.

The work is done by `kahn`. Then `retry` offers the records left over to `accept` once more,
repeating while that accepts any. When `kahn` is right, that pass accepts nothing and costs one
`accept` per leftover record; it is there so that "no leftover record could still be accepted"
(`acceptAll_stuck`) is simple to prove. -/
def acceptAll (c : CheckedStore) (rs : Array Rec) : CheckedStore × Array Rec :=
  let (c', left) := kahn c rs
  retry c' left

/-! ### What `acceptAll` guarantees -/

/-- What stays true while `acceptAll` runs on store `c` and batch `rs`: the current store `cur`
has `c`'s chat, keeps every record of `c`, holds only records of `c` or `rs`, and holds every
record marked done. -/
structure LoopInv (c : CheckedStore) (rs : Array Rec) (cur : CheckedStore) (done : Array Bool) :
    Prop where
  group_eq : cur.group = c.group
  keeps : ∀ (k : Digest) (x : Rec), c.raw.map[k]? = some x → cur.raw.map[k]? = some x
  only : ∀ (k : Digest) (x : Rec), cur.raw.map[k]? = some x → c.raw.map[k]? = some x ∨ x ∈ rs
  done_stored : ∀ (i : Nat) (h : i < rs.size), done[i]? = some true →
    cur.raw.map[hashRecord rs[i]]? = some rs[i]
  size_eq : done.size = rs.size

/-- Accepting a record of the batch keeps the invariant, with the record marked done. -/
theorem LoopInv.accepted {c cur cur' : CheckedStore} {rs : Array Rec} {done : Array Bool}
    {i : Nat} {r : Rec} {d : Digest} (h : LoopInv c rs cur done) (hr : rs[i]? = some r)
    (hacc : cur.accept r = (.accepted d, cur')) :
    LoopInv c rs cur' (done.setIfInBounds i true) := by
  have hraw : rawAccept cur.raw r = (.accepted d, cur'.raw) := by
    have h1 : (cur.accept r).1 = .accepted d := by rw [hacc]
    have h2 : (cur.accept r).2.raw = cur'.raw := by rw [hacc]
    rw [accept_fst] at h1
    rw [accept_raw] at h2
    exact Prod.ext h1 h2
  obtain ⟨rfl, hg, hmap, hold⟩ := rawAccept_accepted hraw
  have hi : i < rs.size := by
    rcases Nat.lt_or_ge i rs.size with h' | h'
    · exact h'
    · simp [Array.getElem?_eq_none h'] at hr
  have hri : rs[i] = r := by simpa [Array.getElem?_eq_getElem hi] using hr
  have hmem : r ∈ rs := hri ▸ Array.getElem_mem hi
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact hg.trans h.group_eq
  · intro k x hk
    have := h.keeps k x hk
    rw [hmap, Std.ExtTreeMap.getElem?_insert]
    split
    · rename_i he
      rw [Std.LawfulEqCmp.compare_eq_iff_eq] at he
      subst he
      rw [hold x this]
    · exact this
  · intro k x hk
    rw [hmap, Std.ExtTreeMap.getElem?_insert] at hk
    split at hk
    · cases hk; exact Or.inr hmem
    · exact h.only k x hk
  · intro j hj hdone
    rw [hmap, Std.ExtTreeMap.getElem?_insert]
    by_cases hji : j = i
    · subst hji
      simp [hri]
    · rw [Array.getElem?_setIfInBounds_ne (Ne.symm hji)] at hdone
      have hs := h.done_stored j hj hdone
      split
      · rename_i he
        rw [Std.LawfulEqCmp.compare_eq_iff_eq] at he
        rw [← he] at hs
        rw [hold _ hs]
      · exact hs
  · simp [h.size_eq]

/-- The worklist loop keeps the invariant. -/
theorem acceptLoop_inv {c : CheckedStore} {rs : Array Rec} (cur : CheckedStore)
    (counts : Array Nat) (waiting : Std.ExtTreeMap Digest (List Nat) compare) (done : Array Bool)
    (ready : List Nat) (h : LoopInv c rs cur done) :
    LoopInv c rs (acceptLoop rs cur counts waiting done ready).1
      (acceptLoop rs cur counts waiting done ready).2 := by
  fun_induction acceptLoop rs cur counts waiting done ready with
  | case1 => exact h
  | case2 _ _ _ _ _ _ _ ih => exact ih h
  | case3 _ _ _ _ _ _ _ hr _ _ hacc _ _ _ _ _ ih => exact ih (h.accepted hr hacc)
  | case4 _ _ _ _ _ _ _ hr _ _ hacc _ _ ih => exact ih (h.accepted hr hacc)
  | case5 cur counts waiting done i ready r hr res c' hres hacc ih =>
    have : c' = cur := by
      have := accept_unchanged (c := cur) (r := r) (by rw [hacc]; exact fun d e => hres d e)
      rwa [hacc] at this
    subst this
    exact ih h

/-- The invariant holds at the start. -/
theorem LoopInv.start (c : CheckedStore) (rs : Array Rec) :
    LoopInv c rs c (Array.replicate rs.size false) where
  group_eq := rfl
  keeps := fun _ _ h => h
  only := fun _ _ h => Or.inl h
  done_stored := fun i h hd => by simp [h] at hd
  size_eq := by simp

/-- A record is left over exactly when it is in the batch and was not marked done. -/
theorem mem_leftovers {rs : Array Rec} {done : Array Bool} (hs : done.size = rs.size)
    {x : Rec} :
    x ∈ leftovers rs done ↔ ∃ (i : Nat) (h : i < rs.size), rs[i] = x ∧ done[i]? = some false := by
  rw [leftovers, Array.mem_filterMap]
  constructor
  · rintro ⟨⟨r, ok⟩, hmem, hf⟩
    obtain ⟨i, hi, he⟩ := Array.mem_iff_getElem.mp hmem
    have hi' : i < rs.size := by simp at hi; omega
    have hid : i < done.size := by simp at hi; omega
    rw [Array.getElem_zip] at he
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    cases hok : done[i] <;> simp [hok] at hf
    exact ⟨i, hi', hf, by simp [hid, hok]⟩
  · rintro ⟨i, hi, rfl, hd⟩
    have hid : i < done.size := by omega
    refine ⟨(rs[i], false), ?_, by simp⟩
    have : done[i] = false := by simpa [hid] using hd
    rw [Array.mem_iff_getElem]
    exact ⟨i, by simp; omega, by simp [Array.getElem_zip, this]⟩

/-- What `kahn` guarantees (whatever order the worklist takes): the chat is the same; every
record of `c` is kept; every stored record comes from `c` or from the batch; every record of the
batch that is not left over is stored under its digest; every left-over record is from the
batch. -/
theorem kahn_sound (c : CheckedStore) (rs : Array Rec) :
    (kahn c rs).1.group = c.group ∧
    (∀ (k : Digest) (x : Rec), c.raw.map[k]? = some x → (kahn c rs).1.raw.map[k]? = some x) ∧
    (∀ (k : Digest) (x : Rec), (kahn c rs).1.raw.map[k]? = some x →
      c.raw.map[k]? = some x ∨ x ∈ rs) ∧
    (∀ x ∈ rs, x ∉ (kahn c rs).2 → (kahn c rs).1.raw.map[hashRecord x]? = some x) ∧
    (∀ x ∈ (kahn c rs).2, x ∈ rs) := by
  unfold kahn
  generalize plan c rs = p
  obtain ⟨counts, waiting, ready⟩ := p
  dsimp only
  have h := acceptLoop_inv c counts waiting (Array.replicate rs.size false) ready
    (LoopInv.start c rs)
  generalize acceptLoop rs c counts waiting (Array.replicate rs.size false) ready = res at h ⊢
  obtain ⟨e, done⟩ := res
  dsimp only
  refine ⟨h.group_eq, h.keeps, h.only, ?_, ?_⟩
  · intro x hx hleft
    obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp hx
    have hid : i < done.size := by rw [h.size_eq]; exact hi
    cases hdi : done[i]
    · exact absurd ((mem_leftovers h.size_eq).mpr ⟨i, hi, rfl, by simp [hid, hdi]⟩) hleft
    · exact h.done_stored i hi (by simp [hid, hdi])
  · intro x hx
    obtain ⟨i, hi, rfl, _⟩ := (mem_leftovers h.size_eq).mp hx
    exact Array.getElem_mem hi

/-- What a store change `c → e` that adds records from `src` and leaves `left` over guarantees:
the chat is the same, `c`'s records are kept, new records come from `src`, records of `src` not
left over are stored under their digest, and left-over records come from `src`. -/
structure Adds (c e : CheckedStore) (src left : List Rec) : Prop where
  group_eq : e.group = c.group
  keeps : ∀ (k : Digest) (x : Rec), c.raw.map[k]? = some x → e.raw.map[k]? = some x
  only : ∀ (k : Digest) (x : Rec), e.raw.map[k]? = some x → c.raw.map[k]? = some x ∨ x ∈ src
  stored : ∀ x ∈ src, x ∉ left → e.raw.map[hashRecord x]? = some x
  left_sub : ∀ x ∈ left, x ∈ src

/-- Two such changes in a row, where the second works on what the first left over. -/
theorem Adds.trans {c d e : CheckedStore} {src mid left : List Rec} (h₁ : Adds c d src mid)
    (h₂ : Adds d e mid left) : Adds c e src left where
  group_eq := h₂.group_eq.trans h₁.group_eq
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

/-- What one pass of `retryPass` does. Started with `keep`, it ends with `keep` followed by the
records it did not accept, and it adds the others. If it accepted none, the store is unchanged
and `accept` refuses each of them. -/
theorem retryPass_spec (c : CheckedStore) (keep : Array Rec) (l : List Rec) :
    (∃ more : List Rec, (retryPass c keep l).2 = keep ++ more.toArray ∧
      Adds c (retryPass c keep l).1 l more ∧ more.length ≤ l.length) ∧
    ((retryPass c keep l).2.size = keep.size + l.length →
      (retryPass c keep l).1 = c ∧ ∀ x ∈ l, ∀ d, (c.accept x).1 ≠ .accepted d) := by
  induction l generalizing c keep with
  | nil =>
    refine ⟨⟨[], by simp [retryPass], ⟨rfl, fun _ _ h => h, fun _ _ h => Or.inl h,
      by simp, by simp⟩, Nat.le_refl _⟩, fun _ => ⟨rfl, by simp⟩⟩
  | cons r rest ih =>
    simp only [retryPass]
    split
    · rename_i d c' hacc
      obtain ⟨⟨more, hmore, hadds, hlen⟩, _⟩ := ih c' keep
      have hstep : Adds c c' [r] [] := by
        have hraw : rawAccept c.raw r = (.accepted d, c'.raw) := by
          have h1 : (c.accept r).1 = .accepted d := by rw [hacc]
          have h2 : (c.accept r).2.raw = c'.raw := by rw [hacc]
          rw [accept_fst] at h1
          rw [accept_raw] at h2
          exact Prod.ext h1 h2
        obtain ⟨rfl, hg, hmap, hold⟩ := rawAccept_accepted hraw
        refine ⟨hg, fun k x hk => ?_, fun k x hk => ?_, fun x hx _ => ?_, by simp⟩
        · rw [hmap, Std.ExtTreeMap.getElem?_insert]
          split
          · rename_i he
            rw [Std.LawfulEqCmp.compare_eq_iff_eq] at he
            subst he
            rw [hold x hk]
          · exact hk
        · rw [hmap, Std.ExtTreeMap.getElem?_insert] at hk
          split at hk
          · cases hk; exact Or.inr (by simp)
          · exact Or.inl hk
        · simp only [List.mem_singleton] at hx
          subst hx
          simp [hmap]
      refine ⟨⟨more, hmore, ?_, by simp; omega⟩, fun hsize => ?_⟩
      · refine ⟨hadds.group_eq.trans hstep.group_eq, fun k x hk => hadds.keeps k x
          (hstep.keeps k x hk), fun k x hk => ?_, fun x hx hl => ?_, fun x hx => ?_⟩
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
      · refine ⟨hadds.group_eq, hadds.keeps, fun k x hk => ?_, fun x hx hl => ?_,
          fun x hx => ?_⟩
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
            (retryPass c (keep.push r) rest).2.size = (keep.push r).size + rest.length := by
          simp at hsize ⊢; omega
        obtain ⟨heq, hrest⟩ := hstuck hsize'
        refine ⟨heq, fun x hx d => ?_⟩
        rcases List.mem_cons.mp hx with rfl | hx'
        · rw [hacc]; exact fun h => hres d h
        · exact hrest x hx' d

/-- What `retry` guarantees: it adds records as `Adds` says, and `accept` refuses every record it
leaves over, in the final store. -/
theorem retry_spec (c : CheckedStore) (left : Array Rec) :
    Adds c (retry c left).1 left.toList (retry c left).2.toList ∧
      ∀ x ∈ (retry c left).2, ∀ d, ((retry c left).1.accept x).1 ≠ .accepted d := by
  fun_induction retry c left with
  | case1 c left c' keep hpass hlt ih =>
    rw [hpass]
    dsimp only
    simp only [hlt, ↓reduceIte]
    obtain ⟨⟨more, hmore, hadds, _⟩, _⟩ := retryPass_spec c #[] left.toList
    rw [hpass] at hmore hadds
    dsimp only at hmore hadds
    subst hmore
    simp only [List.toList_toArray, Array.empty_append] at ih hadds ⊢
    exact ⟨hadds.trans ih.1, ih.2⟩
  | case2 c left c' keep hpass hge =>
    rw [hpass]
    dsimp only
    simp only [hge, ↓reduceIte]
    obtain ⟨⟨more, hmore, hadds, hlen⟩, hstuck⟩ := retryPass_spec c #[] left.toList
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

/-- **What `acceptAll` guarantees.** The chat is the same; every record of `c` is kept; every
stored record comes from `c` or from the batch; every record of the batch that is not left over is
stored under its digest; every left-over record is from the batch. So a mistake in the worklist
could only leave records over, never add a wrong one or lose one. -/
theorem acceptAll_sound (c : CheckedStore) (rs : Array Rec) :
    (c.acceptAll rs).1.group = c.group ∧
    (∀ (k : Digest) (x : Rec), c.raw.map[k]? = some x → (c.acceptAll rs).1.raw.map[k]? = some x) ∧
    (∀ (k : Digest) (x : Rec), (c.acceptAll rs).1.raw.map[k]? = some x →
      c.raw.map[k]? = some x ∨ x ∈ rs) ∧
    (∀ x ∈ rs, x ∉ (c.acceptAll rs).2 → (c.acceptAll rs).1.raw.map[hashRecord x]? = some x) ∧
    (∀ x ∈ (c.acceptAll rs).2, x ∈ rs) := by
  obtain ⟨hg, hkeep, honly, hstored, hsub⟩ := kahn_sound c rs
  have hk : Adds c (kahn c rs).1 rs.toList (kahn c rs).2.toList :=
    ⟨hg, hkeep, fun k x hx => by simpa using honly k x hx,
      fun x hx hl => hstored x (by simpa using hx) (by simpa using hl),
      fun x hx => by simpa using hsub x (by simpa using hx)⟩
  have h := hk.trans (retry_spec (kahn c rs).1 (kahn c rs).2).1
  unfold acceptAll
  refine ⟨h.group_eq, h.keeps, fun k x hx => by simpa using h.only k x hx,
    fun x hx hl => h.stored x (by simpa using hx) (by simpa using hl),
    fun x hx => by simpa using h.left_sub x (by simpa using hx)⟩

/-- **Nothing left over could still be accepted:** `accept` refuses every left-over record in
the final store. -/
theorem acceptAll_stuck (c : CheckedStore) (rs : Array Rec) :
    ∀ x ∈ (c.acceptAll rs).2, ∀ d, ((c.acceptAll rs).1.accept x).1 ≠ .accepted d :=
  (retry_spec (kahn c rs).1 (kahn c rs).2).2

/-! ## Loading and merging -/

/-- The digest of every given record, next to the record. -/
def withDigests (rs : Array Rec) : Array (Digest × Rec) := rs.map fun r => (hashRecord r, r)

/-- The smallest digest at which two different records meet: a given record and a stored one,
or two given records. `none` if there is no such digest. -/
def findCollision (c : CheckedStore) (left : Array (Digest × Rec)) : Option Digest :=
  let (_, found) := left.foldl (init := ((∅ : RecMap), (∅ : DigestSet))) fun (seen, found) (d, r) =>
    match (c.get d).orElse fun _ => seen[d]? with
    | some other => if other = r then (seen, found) else (seen, found.insert d)
    | none => (seen.insert d r, found)
  found.min?

/-- For records that were not accepted: their digests, and the digests their links point to that
are neither stored nor one of these records. Both sorted. -/
def leftoverReport (c : CheckedStore) (left : Array (Digest × Rec)) :
    Array Digest × Array Digest :=
  let dropped : DigestSet := left.foldl (fun s (d, _) => s.insert d) ∅
  let missing : DigestSet := left.foldl (init := ∅) fun s (_, r) =>
    r.links.foldl (init := s) fun s l => if c.has l || dropped.contains l then s else s.insert l
  (dropped.toList.toArray, missing.toList.toArray)

end CheckedStore

/-- Why a store could not be loaded (`open`, `salvage`) or merged. These are the error replies of
`OPEN`, `SALVAGE` and `MERGE` (docs/PLAN.md §3.3). -/
inductive OpenError
  /-- The bytes are not a store blob. -/
  | malformed
  /-- Too many records, a record with too many links, or a merge that would overfill the
  store. -/
  | tooLarge
  /-- The blob, or a record in it, belongs to another chat. -/
  | wrongChat
  /-- Two different records have digest `d`. -/
  | collision (d : Digest)
  /-- Some records can never be accepted (`records`, their digests): a link points to nothing
  (`missing`, those link digests), or the records link each other in a cycle. -/
  | unverifiable (records : Array Digest) (missing : Array Digest)
deriving DecidableEq, Repr

namespace CheckedStore

/-- Why `acceptAll` left records over, as an error reply: a collision if there is one, then a full
store, otherwise the records that cannot be accepted and the digests they lack. -/
def explain (c : CheckedStore) (left : Array Rec) : OpenError :=
  let left := withDigests left
  match findCollision c left with
  | some d => .collision d
  | none =>
    if maxRecords ≤ c.size + 1 then .tooLarge
    else
      let (records, missing) := leftoverReport c left
      .unverifiable records missing

/-- Whether every record belongs to chat `g`. -/
def allInChat (g : GroupId) (u : Array Rec) : Bool := u.all fun r => r.group == g

/-- The checks `open` and `salvage` make before accepting anything: the size limits, then the
chat of every record. -/
def checkInput (g : GroupId) (u : Array Rec) : Option OpenError :=
  if WellSized u then (if allInChat g u then none else some .wrongChat) else some .tooLarge

/-- Load the records `u` as a new store of chat `g`. Every record must be accepted; otherwise
nothing is loaded and the error says why. -/
def openRecords (g : GroupId) (u : Array Rec) : Except OpenError CheckedStore :=
  match checkInput g u with
  | some e => .error e
  | none =>
    let (c, left) := acceptAll (empty g) u
    if left.isEmpty then .ok c else .error (explain c left)

/-- Load a store blob as the store of chat `g` (`OPEN`). It succeeds only if every record in the
blob is accepted. The heads are recomputed. -/
def «open» (g : GroupId) (b : ByteArray) : Except OpenError CheckedStore :=
  match decodeBlob b with
  | none => .error .malformed
  | some (g', u) => if g' ≠ g then .error .wrongChat else openRecords g u

/-- The result of `salvage`: the store of the records that were accepted, the digests of the
records that were dropped, and the digests the dropped records link that point to nothing. -/
structure Salvaged where
  /-- The accepted records. -/
  store : CheckedStore
  /-- The digests of the records that were not accepted, sorted. -/
  dropped : Array Digest
  /-- The link digests of the dropped records that point to no record, sorted. -/
  missing : Array Digest

/-- Load as many of the records `u` as can be accepted, as a new store of chat `g`, and name the
rest. It refuses (loads nothing) if the input is too large, holds a record of another chat, or
holds two different records with the same digest. -/
def salvageRecords (g : GroupId) (u : Array Rec) : Except OpenError Salvaged :=
  match checkInput g u with
  | some e => .error e
  | none =>
    let (c, left) := acceptAll (empty g) u
    let left := withDigests left
    match findCollision c left with
    | some d => .error (.collision d)
    | none =>
      let (dropped, missing) := leftoverReport c left
      .ok ⟨c, dropped, missing⟩

/-- `salvageRecords` on a store blob (`SALVAGE`). -/
def salvage (g : GroupId) (b : ByteArray) : Except OpenError Salvaged :=
  match decodeBlob b with
  | none => .error .malformed
  | some (g', u) => if g' ≠ g then .error .wrongChat else salvageRecords g u

/-- Add every record of the store `d` to `c`. Succeeds only if every record is accepted; on an
error the caller keeps `c` unchanged. -/
def merge (c d : CheckedStore) : Except OpenError CheckedStore :=
  if d.group ≠ c.group then .error .wrongChat
  else
    let (e, left) := acceptAll c d.records
    if left.isEmpty then .ok e else .error (explain e left)

/-- `MERGE`: open the blob as a store of `c`'s chat (with all of `open`'s checks), then merge it
into `c`. -/
def mergeBlob (c : CheckedStore) (b : ByteArray) : Except OpenError CheckedStore :=
  match CheckedStore.open c.group b with
  | .error e => .error e
  | .ok d => c.merge d

/-! ### What `merge` and `open` guarantee -/

/-- A successful merge holds exactly the records of both stores, and keeps `c`'s chat. -/
theorem merge_ok {c d e : CheckedStore} (h : c.merge d = .ok e) :
    e.group = c.group ∧ ∀ (k : Digest) (x : Rec),
      e.raw.map[k]? = some x ↔ c.raw.map[k]? = some x ∨ d.raw.map[k]? = some x := by
  unfold merge at h
  split at h
  · simp at h
  obtain ⟨hg, hkeep, honly, hall, _⟩ := acceptAll_sound c d.records
  generalize c.acceptAll d.records = res at h hg hkeep honly hall
  obtain ⟨e', left⟩ := res
  dsimp only at h hg hkeep honly hall
  split at h
  · rename_i hleft
    simp only [Except.ok.injEq] at h
    subst e
    have hnil : ∀ x, x ∉ left := by
      intro x hx; simp_all [Array.isEmpty_iff]
    refine ⟨hg, fun k x => ⟨fun hk => ?_, ?_⟩⟩
    · rcases honly k x hk with hc | hd
      · exact Or.inl hc
      · obtain ⟨k', hk'⟩ := mem_records.mp hd
        have h1 := d.built.hash_eq k' x hk'
        have h2 := e'.built.hash_eq k x hk
        exact Or.inr (by rw [← h2, h1]; exact hk')
    · rintro (hc | hd)
      · exact hkeep k x hc
      · have := hall x (mem_records.mpr ⟨k, hd⟩) (hnil x)
        rwa [d.built.hash_eq k x hd] at this
  · simp at h

/-- A successful `openRecords` holds exactly the given records, each under its digest; the input
was within the size limits and all of chat `g`. -/
theorem openRecords_ok {g : GroupId} {u : Array Rec} {c : CheckedStore}
    (h : openRecords g u = .ok c) :
    c.group = g ∧ WellSized u ∧ (∀ r ∈ u, r.group = g) ∧
      ∀ (k : Digest) (x : Rec), c.raw.map[k]? = some x ↔ x ∈ u ∧ hashRecord x = k := by
  unfold openRecords at h
  split at h
  · simp at h
  rename_i hcheck
  have hws : WellSized u := by
    unfold checkInput at hcheck
    by_cases hw : WellSized u
    · exact hw
    · simp [hw] at hcheck
  have hchat : ∀ r ∈ u, r.group = g := by
    unfold checkInput at hcheck
    simp only [hws, ↓reduceIte] at hcheck
    intro r hr
    split at hcheck
    · rename_i hall
      simp only [allInChat, Array.all_eq_true_iff_forall_mem, beq_iff_eq] at hall
      exact hall r hr
    · simp at hcheck
  obtain ⟨hg, _, honly, hall, _⟩ := acceptAll_sound (empty g) u
  generalize (empty g).acceptAll u = res at h hg honly hall
  obtain ⟨e, left⟩ := res
  dsimp only at h hg honly hall
  split at h
  · rename_i hleft
    simp only [Except.ok.injEq] at h
    subst c
    have hnil : ∀ x, x ∉ left := by
      intro x hx; simp_all [Array.isEmpty_iff]
    refine ⟨hg, hws, hchat, fun k x => ⟨fun hk => ?_, ?_⟩⟩
    · rcases honly k x hk with he | hu
      · simp [empty] at he
      · exact ⟨hu, e.built.hash_eq k x hk⟩
    · rintro ⟨hu, rfl⟩
      exact hall x hu (hnil x)
  · simp at h

/-- A map whose keys are all digests of records of `u`, and which misses the digest of one record
of `u`, has fewer keys than `u` has entries. -/
theorem size_lt_of_keys {β : Type} {m : Std.ExtTreeMap Digest β compare} {u : Array Rec}
    {r : Rec} (hk : ∀ k ∈ m, ∃ x ∈ u, hashRecord x = k) (hr : r ∈ u) (hn : hashRecord r ∉ m) :
    m.size < u.size := by
  rw [← Std.ExtTreeMap.length_keys]
  have hsub : m.keys ⊆ (u.toList.map hashRecord).filter (· != hashRecord r) := by
    intro k hkm
    have hkm' := Std.ExtTreeMap.mem_keys.mp hkm
    obtain ⟨x, hx, rfl⟩ := hk _ hkm'
    simp only [List.mem_filter, List.mem_map, Array.mem_toList_iff, bne_iff_ne, ne_eq]
    exact ⟨⟨x, hx, rfl⟩, fun h => hn (h ▸ hkm')⟩
  have h1 := Std.ExtTreeMap.nodup_keys.length_le_of_subset hsub
  have h2 : ((u.toList.map hashRecord).filter (· != hashRecord r)).length <
      (u.toList.map hashRecord).length :=
    List.length_filter_lt_length_iff_exists.mpr
      ⟨hashRecord r, List.mem_map.mpr ⟨r, by simpa using hr, rfl⟩, by simp⟩
  simp only [List.length_map, Array.length_toList] at h2
  omega

/-- **Completeness of `openRecords`.** Records within the size limits, all of chat `g`, with no
two different records sharing a digest, and that can be listed in an accept order, are all
loaded. -/
theorem openRecords_complete {g : GroupId} {u : Array Rec} (hw : WellSized u)
    (hg : ∀ r ∈ u, r.group = g)
    (hcol : ∀ x ∈ u, ∀ y ∈ u, hashRecord x = hashRecord y → x = y)
    (hord : ∃ l, AcceptOrder l ∧ ∀ r, r ∈ l ↔ r ∈ u) :
    ∃ c, openRecords g u = .ok c := by
  have hchat : allInChat g u = true := by
    simp only [allInChat, Array.all_eq_true_iff_forall_mem, beq_iff_eq]
    exact hg
  have hcheck : checkInput g u = none := by simp [checkInput, hw, hchat]
  unfold openRecords
  rw [hcheck]
  dsimp only
  obtain ⟨hgrp, _, honly, hstored, hleftsub⟩ := acceptAll_sound (empty g) u
  have hstuck := acceptAll_stuck (empty g) u
  generalize (empty g).acceptAll u = res at hgrp honly hstored hleftsub hstuck ⊢
  obtain ⟨e, left⟩ := res
  dsimp only at hgrp honly hstored hleftsub hstuck ⊢
  have honly' : ∀ k x, e.raw.map[k]? = some x → x ∈ u := fun k x hk =>
    (honly k x hk).resolve_left (by simp [empty])
  have hegrp : e.raw.group = g := hgrp
  -- `accept` takes any record of `u` whose links are all stored.
  have hok : ∀ x ∈ u, (∀ d ∈ x.links, d ∈ e.raw.map) →
      (rawAccept e.raw x).1 = .accepted (hashRecord x) := by
    intro x hx hl
    apply rawAccept_of_ok ((hg x hx).trans hegrp.symm) (hw.2 x hx) hl
    · intro old hold
      exact hcol old (honly' _ _ hold) x hx (e.built.hash_eq _ _ hold)
    · intro hn
      have := size_lt_of_keys (m := e.raw.map) (u := u) (r := x) (fun k hk => by
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
      exact hok x hxu (fun d hd => e.built.closed _ x hs d hd))
  simp [hleft]

/-- **A store reopens as itself:** opening the blob of a store, under its own chat, gives back
exactly that store (the maps are extensional, so `=` compares contents). -/
theorem encode_reopens (c : CheckedStore) : CheckedStore.open c.group c.encode = .ok c := by
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
  unfold CheckedStore.open encode
  rw [decodeBlob_encodeBlob _ _ hws]
  dsimp only
  simp only [ne_eq, not_true_eq_false, ↓reduceIte]
  obtain ⟨e, he⟩ := openRecords_complete hws
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
  change openRecords c.raw.group c.records = .ok c
  rw [he]
  obtain ⟨hgrp, _, _, hemap⟩ := openRecords_ok he
  have hmap : e.raw.map = c.raw.map := by
    apply Std.ExtTreeMap.ext_getElem?
    intro k
    apply Option.ext
    intro x
    rw [hemap k x, hkey k x]
  have hheads : e.raw.heads = c.raw.heads := by
    apply Std.ExtTreeSet.ext_mem
    intro d
    rw [e.built.heads_iff, c.built.heads_iff, hmap]
  congr 1
  apply ext
  have hg' : e.raw.group = c.raw.group := hgrp
  cases he' : e.raw
  cases hc' : c.raw
  rw [he', hc'] at hg' hmap hheads
  simp only at hg' hmap hheads
  rw [hg', hmap, hheads]

end CheckedStore

/-! ## Example: a small chat

Alice writes `a1`. Bob and Carol both reply to it at the same time (`b1`, `c1`). Alice then
writes `a2`, which links both replies. The outputs below are checked by `#guard_msgs` when this
file is built. -/

namespace Examples

/-- Bob's account id. -/
def bob : Aci := ⟨⟨Array.replicate 16 0xb0⟩, rfl⟩

/-- Carol's account id. -/
def carol : Aci := ⟨⟨Array.replicate 16 0xca⟩, rfl⟩

/-- Alice's first message. -/
def a1 : Rec := Rec.make group (dig 0xa1) #[] alice

/-- Bob's reply to `a1`. -/
def b1 : Rec := Rec.make group (dig 0xb1) #[hashRecord a1] bob

/-- Carol's reply to `a1`, written at the same time as `b1`. -/
def c1 : Rec := Rec.make group (dig 0xc1) #[hashRecord a1] carol

/-- Alice's second message, after both replies. -/
def a2 : Rec := Rec.make group (dig 0xa2) #[hashRecord b1, hashRecord c1] alice

/-- The example records with their names. -/
def named : List (Rec × String) := [(a1, "a1"), (b1, "b1"), (c1, "c1"), (a2, "a2")]

/-- The name of an example record's digest, or the first 8 hex digits of any other digest. -/
def nameOf (d : Digest) : String :=
  match named.find? (fun (r, _) => hashRecord r == d) with
  | some (_, n) => n
  | none => String.ofList (d.toHex.toList.take 8)

/-- `nameOf` on each digest. -/
def names (ds : Array Digest) : Array String := ds.map nameOf

/-- An `accept` result, with names for digests. -/
def showResult : AcceptResult → String
  | .accepted d => s!"accepted {nameOf d}"
  | .missing ds => s!"missing {names ds}"
  | .collision d => s!"collision {nameOf d}"
  | .wrongChat => "wrongChat"
  | .tooLarge => "tooLarge"

/-- An `open` or `merge` result, with names for digests. -/
def showOpen : Except OpenError CheckedStore → String
  | .ok c => s!"ok, heads {names c.headsArray}, {c.size} records"
  | .error (.collision d) => s!"collision {nameOf d}"
  | .error (.unverifiable u m) => s!"unverifiable {names u}, missing {names m}"
  | .error e => (reprStr e).replace "Zrdt.OpenError." ""

/-- The store after accepting `a1`. -/
def s1 : CheckedStore := ((CheckedStore.empty group).accept a1).2

/-- The store after accepting `a1` and `b1`. -/
def s2 : CheckedStore := (s1.accept b1).2

/-- The store with all four records. -/
def all4 : CheckedStore := ((CheckedStore.empty group).acceptAll #[a2, c1, b1, a1]).1

/-- The blob of `all4` with `b1` cut out: `a2` links a record that is not there. -/
def doctored : ByteArray := encodeBlob group #[a1, c1, a2]

/-- A record with 4097 different links, one more than allowed. -/
def tooManyLinks : Rec :=
  Rec.make group (dig 0) ((Array.range 4097).map fun i =>
    ⟨⟨(u32be i).data ++ Array.replicate 28 0⟩, by simp [ByteArray.size, u32be]⟩) alice

/-- The store holding `a1` and `b1`. -/
def storeAB : CheckedStore := ((CheckedStore.empty group).acceptAll #[a1, b1]).1

/-- The store holding `a1` and `c1`. -/
def storeAC : CheckedStore := ((CheckedStore.empty group).acceptAll #[a1, c1]).1

end Examples

open Examples CheckedStore

-- `accept`: the first message is accepted and becomes the only head.
/-- info: "accepted a1" -/
#guard_msgs in #eval showResult ((empty group).accept a1).1
/-- info: #["a1"] -/
#guard_msgs in #eval names s1.headsArray

-- A gap: `a2` arrives before the replies it links. The store is unchanged.
/-- info: "missing #[c1, b1]" -/
#guard_msgs in #eval showResult (s1.accept a2).1
/-- info: 1 -/
#guard_msgs in #eval (s1.accept a2).2.size

-- `b1` resolves; it replaces `a1` as the head. Accepting `a1` again changes nothing.
/-- info: "accepted b1" -/
#guard_msgs in #eval showResult (s1.accept b1).1
/-- info: #["b1"] -/
#guard_msgs in #eval names s2.headsArray
/-- info: ("accepted a1", 2) -/
#guard_msgs in #eval (showResult (s2.accept a1).1, (s2.accept a1).2.size)

-- Refusals: another chat; too many links; a different record under the same digest (made on a
-- raw store, since a real SHA-256 collision is not available).
/-- info: "wrongChat" -/
#guard_msgs in #eval showResult (s2.accept (Rec.make otherGroup (dig 0xd1) #[] alice)).1
/-- info: "tooLarge" -/
#guard_msgs in #eval showResult (s2.accept tooManyLinks).1
/-- info: "collision a1" -/
#guard_msgs in #eval showResult (rawAccept ⟨group, (∅ : RecMap).insert (hashRecord a1) b1, ∅⟩ a1).1

-- `acceptAll` takes the records in any order. Without `c1`, `a2` is left over.
/-- info: (#["a2"], 4, 0) -/
#guard_msgs in #eval
  let (c, left) := (empty group).acceptAll #[a2, c1, b1, a1]
  (names c.headsArray, c.size, left.size)
/-- info: (#["b1"], #["a2"]) -/
#guard_msgs in #eval
  let (c, left) := (empty group).acceptAll #[a2, b1, a1]
  (names c.headsArray, left.map (nameOf ∘ hashRecord))

-- `has`, `get`, `reachSet`. From `c1` you reach `c1` and `a1`; from `a2`, everything. A start
-- digest that is not stored is left out.
/-- info: (true, true, false) -/
#guard_msgs in #eval
  (all4.has (hashRecord c1), all4.get (hashRecord c1) == some c1, all4.has (dig 0))
/-- info: #["a1", "c1"] -/
#guard_msgs in #eval names (all4.reachSet #[hashRecord c1]).toList.toArray
/-- info: #["a1", "c1", "b1", "a2"] -/
#guard_msgs in #eval names (all4.reachSet #[hashRecord a2, dig 0]).toList.toArray

-- `encode` and `open`: the blob opens to the same store. Wrong chat and bad bytes are refused.
/-- info: 542 -/
#guard_msgs in #eval all4.encode.size
/-- info: "ok, heads #[a2], 4 records" -/
#guard_msgs in #eval showOpen (CheckedStore.open group all4.encode)
#guard match CheckedStore.open group all4.encode with
  | .ok c => c.encode == all4.encode
  | .error _ => false
/-- info: "wrongChat" -/
#guard_msgs in #eval showOpen (CheckedStore.open otherGroup all4.encode)
/-- info: "malformed" -/
#guard_msgs in #eval showOpen (CheckedStore.open group (all4.encode.push 0))

-- A doctored restore: `b1` was cut out. `open` refuses and names what is missing; `salvage`
-- keeps what checks and names what it dropped.
/-- info: "unverifiable #[a2], missing #[b1]" -/
#guard_msgs in #eval showOpen (CheckedStore.open group doctored)
/-- info: "heads #[c1], dropped #[a2], missing #[b1]" -/
#guard_msgs in #eval
  match salvage group doctored with
  | .ok sv =>
    s!"heads {names sv.store.headsArray}, dropped {names sv.dropped}, missing {names sv.missing}"
  | .error e => reprStr e

-- `merge`: two members' stores, each with one of the parallel replies.
/-- info: "ok, heads #[c1, b1], 3 records" -/
#guard_msgs in #eval showOpen (storeAB.merge storeAC)
/-- info: "ok, heads #[c1, b1], 3 records" -/
#guard_msgs in #eval showOpen (storeAB.mergeBlob storeAC.encode)
/-- info: "wrongChat" -/
#guard_msgs in #eval showOpen (storeAB.merge (empty otherGroup))

-- `AcceptOrder`, newest first: `b1` links `a1`, which is further down. The other way round,
-- `b1` would be accepted before what it links.
example : AcceptOrder [b1, a1] :=
  .cons (fun d hd => ⟨a1, by simp, by simp [b1] at hd; exact hd.symm⟩)
    (.cons (fun d hd => by simp [a1] at hd) .nil)
example : ¬ AcceptOrder [a1, b1] := by
  rintro (_ | ⟨_, _ | ⟨h, _⟩⟩)
  simpa using h (hashRecord a1) (by simp [b1])

-- `missingLinks` and `records` (sorted by digest).
#guard missingLinks s1.raw.map a2 == #[hashRecord c1, hashRecord b1]
#guard (names (all4.records.map hashRecord)) == #["a1", "c1", "b1", "a2"]

-- `plan`: with an empty store, `a1` waits for nothing; `a2` waits for two digests.
#guard let (counts, waiting, ready) := plan (empty group) #[a2, c1, b1, a1]
  counts == #[2, 1, 1, 0] && waiting.size == 3 && ready == [3]

-- `findCollision` and `leftoverReport` on the doctored restore: no collision; `a2` is dropped
-- and `b1` is missing.
#guard let (c, left) := (empty group).acceptAll #[a1, c1, a2]
  findCollision c (withDigests left) == none &&
    leftoverReport c (withDigests left) == (#[hashRecord a2], #[hashRecord b1])
#guard findCollision all4 #[(hashRecord a1, b1)] == some (hashRecord a1)

-- `checkInput`.
#guard checkInput group #[a1, b1] == none
#guard checkInput otherGroup #[a1] == some .wrongChat

-- The guarantees, on concrete inputs with every hypothesis discharged.
example : CheckedStore.open all4.group all4.encode = .ok all4 := encode_reopens all4
example : ∃ c, openRecords group #[a1] = .ok c :=
  openRecords_complete (by decide) (by simp [a1]) (by simp)
    ⟨[a1], .cons (by simp [a1]) .nil, by simp⟩
example : ((empty group).accept a1).1 = .accepted (hashRecord a1) := by
  rw [accept_fst]
  exact rawAccept_of_ok rfl (by decide) (by simp [a1]) (by simp [empty])
    (fun _ => by simp [empty, maxRecords])

-- `Built` rejects bad stores: a record of another chat, and a head that is not stored.
example : ¬ Built ⟨group, (∅ : RecMap).insert (dig 0) (Rec.make otherGroup (dig 1) #[] alice), ∅⟩ :=
  fun h => absurd (h.group_eq (dig 0) (Rec.make otherGroup (dig 1) #[] alice) (by simp))
    (by decide)
example : ¬ Built ⟨group, ∅, (∅ : DigestSet).insert (dig 1)⟩ :=
  fun h => by simpa using ((h.heads_iff (dig 1)).mp (by simp)).1

end Zrdt
