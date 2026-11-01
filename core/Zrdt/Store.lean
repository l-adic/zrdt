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
algorithm). It returns the records it could not add. `open` (load a saved store), `salvage` (load
the part that checks) and `merge` (add another store) are built on it.

**Observers:** `heads`, `has`, `get`, `reachSet` (the records reached by following links) and
`encode` (the store blob, records sorted by digest).

The maps are `Std.ExtTreeMap` and `Std.ExtTreeSet`: two maps with the same contents are equal
(`=`), whatever order the records were added in.
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
    c' = c ∧ ds ≠ #[] ∧ (∀ x, x ∈ ds ↔ x ∈ r.links ∧ x ∉ c.map) ∧ ds = missingLinks c.map r := by
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
      refine ⟨rfl, ?_, fun x => mem_missingLinks, rfl⟩
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

/-- Accept a batch of records, in any order that lets their links resolve (Kahn's algorithm).
Every record goes through `accept`. Returns the new store and the records that were not accepted,
in input order. -/
def acceptAll (c : CheckedStore) (rs : Array Rec) : CheckedStore × Array Rec :=
  let (counts, waiting, ready) := plan c rs
  let (c', done) := acceptLoop rs c counts waiting (Array.replicate rs.size false) ready
  (c', (rs.zip done).filterMap fun (r, ok) => if ok then none else some r)

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

-- `Built` rejects bad stores: a record of another chat, and a head that is not stored.
example : ¬ Built ⟨group, (∅ : RecMap).insert (dig 0) (Rec.make otherGroup (dig 1) #[] alice), ∅⟩ :=
  fun h => absurd (h.group_eq (dig 0) (Rec.make otherGroup (dig 1) #[] alice) (by simp))
    (by decide)
example : ¬ Built ⟨group, ∅, (∅ : DigestSet).insert (dig 1)⟩ :=
  fun h => by simpa using ((h.heads_iff (dig 1)).mp (by simp)).1

end Zrdt
