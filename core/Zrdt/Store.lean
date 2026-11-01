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
  heads_iff : ∀ d, d ∈ c.heads ↔ d ∈ c.map ∧ ∀ (k : Digest) (r : Rec), c.map[k]? = some r → d ∉ r.links
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

/-- Accept one record (see `rawAccept`). Returns what happened and the new store. -/
def accept (c : CheckedStore) (r : Rec) : AcceptResult × CheckedStore :=
  let p := rawAccept c.raw r
  (p.1, ⟨p.2, rawAccept_built c.built r⟩)

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

/-- Erasing a key that is present makes a map smaller (used to show the loops below end). -/
theorem size_erase_lt {β : Type} {m : Std.ExtTreeMap Digest β compare} {d : Digest}
    (h : d ∈ m) : (m.erase d).size < m.size := by
  rw [Std.ExtTreeMap.size_erase]
  simp only [Std.ExtTreeMap.mem_iff_contains.mp h, ↓reduceIte]
  have : m.size ≠ 0 := by
    intro h0
    rw [← Std.ExtTreeMap.eq_empty_iff_size_eq_zero] at h0
    simp [h0] at h
  omega

/-- Follow links from the digests in `todo`. `left` holds the stored records not reached yet,
and `seen` the digests reached so far. A digest that is not stored is skipped. -/
def reachLoop (left : RecMap) (seen : DigestSet) : List Digest → DigestSet
  | [] => seen
  | d :: todo =>
    if h : d ∈ left then
      reachLoop (left.erase d) (seen.insert d) ((left.get d h).links.toList ++ todo)
    else reachLoop left seen todo
termination_by todo => (left.size, todo.length)
decreasing_by
  · exact Prod.Lex.left _ _ (size_erase_lt h)
  · exact Prod.Lex.right _ (by simp)

/-- The stored records reached from the digests `start` by following links, as their digests.
A start digest that is not stored is left out. -/
def reachSet (c : CheckedStore) (start : Array Digest) : DigestSet :=
  reachLoop c.raw.map ∅ start.toList

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

/-- Load the records `u` as a new store of chat `g`. Every record must be accepted; otherwise
nothing is loaded and the error says why. -/
def openRecords (g : GroupId) (u : Array Rec) : Except OpenError CheckedStore :=
  if ¬ WellSized u then .error .tooLarge
  else if u.any (fun r => r.group != g) then .error .wrongChat
  else
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
  if ¬ WellSized u then .error .tooLarge
  else if u.any (fun r => r.group != g) then .error .wrongChat
  else
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

end Zrdt
