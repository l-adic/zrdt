import Zrdt.RelStore
import Zrdt.Serve
import Zrdt.Provenance

/-!
# A chat's store, closed or relative, and its blob `zrdtS3` (docs/JOIN_PLAN.md §3.3, §6.2)

**`ChatStore`.** `zrdtd` holds, for each open chat, either a **closed** store (`CheckedStore`: a
genesis member's, or one restored from a closed blob) or a **relative** store (`RelStore`: one
created for a catch-up, `NEW_RELATIVE`). A closed store runs exactly the code it ran before
(`CheckedStore.accept`, `merge`, `open`, `classify`), so every theorem about those covers it. A
closed store never takes a boundary digest.

**The blob `zrdtS3`** (`ENCODE`, `OPEN`, `SALVAGE`, `MERGE`), all numbers big-endian:

    "zrdtS3" ‖ mode (u8: 0 closed, 1 relative)
      ‖ n (u32) ‖ n × (digest (32) ‖ voucher aci (16))          the boundary, sorted by digest
      ‖ m (u32) ‖ m × (digest (32) ‖ len (u32) ‖ field-201 value) the audience table, sorted
      ‖ the records: a `zrdtS2` blob (`encodeBlob`), to the end

A closed blob has `n = 0`. The audience table holds the audience `zrdtd` recorded from a checked
opening, for stored records only; each value is read back with `Serve.parseAudience`. The table
decides structure only (`Serve.serve_content` does not mention it). The project is greenfield:
`OPEN` reads `zrdtS3` only.

**Proved here:** `decodeChat_encodeChat` (the framing reads back what was written) and
`ChatStore.encode_reopens`: opening a store's blob under its own chat gives back exactly that
store, and its audience table for stored records (every audience reads back,
`Serve.parseAudience_writeAudience`). `MERGE` records the blob's audiences of the records stored
in the merged store that have none recorded (`mergeAudiences_spec`).
-/

namespace Zrdt

/-- The store of an open chat. -/
inductive ChatStore
  /-- A closed store: every link resolves to a stored record. -/
  | closed (c : CheckedStore)
  /-- A relative store: links may resolve to boundary digests (a newcomer's store). -/
  | relative (c : RelStore)

/-- The audiences `zrdtd` recorded from openings it checked, by record digest. -/
abbrev AudTable := Std.ExtTreeMap Digest (Array Serve.Seat) compare

namespace ChatStore

/-- The records and heads. -/
def raw : ChatStore → RawStore
  | .closed c => c.raw
  | .relative c => c.raw

/-- The chat. -/
def group (s : ChatStore) : GroupId := s.raw.group

/-- Whether the store is relative. -/
def isRelative : ChatStore → Bool
  | .closed _ => false
  | .relative _ => true

/-- The boundary with its vouchers (empty for a closed store). -/
def boundary : ChatStore → Boundary
  | .closed _ => ∅
  | .relative c => c.boundary

/-- The boundary digests the store holds no record for (empty for a closed store). -/
def boundaryDigests : ChatStore → DigestSet
  | .closed _ => ∅
  | .relative c => c.boundaryDigests

/-- The heads, as a sorted array (`HEADS`): stored digests and boundary digests no record links. -/
def headsArray : ChatStore → Array Digest
  | .closed c => c.headsArray
  | .relative c => c.headsArray

/-- Whether a record with digest `d` is stored. -/
def has (s : ChatStore) (d : Digest) : Bool := s.raw.map.contains d

/-- The record with digest `d`, if stored. -/
def get (s : ChatStore) (d : Digest) : Option Rec := s.raw.map[d]?

/-- The stored records, sorted by digest. -/
def records : ChatStore → Array Rec
  | .closed c => c.records
  | .relative c => c.records

/-- The `zrdtS2` blob of the records. -/
def inner : ChatStore → ByteArray
  | .closed c => c.encode
  | .relative c => encodeBlob c.group c.records

/-- What a store is correct relative to: its own boundary. -/
theorem builtRel : (s : ChatStore) → BuiltRel s.raw s.boundary
  | .closed c => builtRel_empty_iff.mpr c.built
  | .relative c => c.built

/-- The store as a relative store (a closed store has an empty boundary). -/
def toRel : ChatStore → RelStore
  | .closed c => .ofChecked c
  | .relative c => c

/-- The stored records reached from `start` by following links (`REACH_SET`). -/
def reachSet (s : ChatStore) (start : Array Digest) : DigestSet := s.raw.reachSet start

/-- Accept one record: `CheckedStore.accept` for a closed store, `RelStore.accept` for a relative
one. -/
def accept : ChatStore → Rec → AcceptResult × ChatStore
  | .closed c, r => let p := c.accept r; (p.1, .closed p.2)
  | .relative c, r => let p := c.accept r; (p.1, .relative p.2)

/-- Accept a batch: `CheckedStore.acceptAll` for a closed store, `RelStore.acceptAll` for a
relative one. -/
def acceptAll : ChatStore → Array Rec → ChatStore × Array Rec
  | .closed c, rs => let p := c.acceptAll rs; (.closed p.1, p.2)
  | .relative c, rs => let p := c.acceptAll rs; (.relative p.1, p.2)

/-- Accepting keeps the kind of store. -/
theorem isRelative_accept (s : ChatStore) (r : Rec) : (s.accept r).2.isRelative = s.isRelative := by
  cases s <;> rfl

/-- Accepting a batch keeps the kind of store. -/
theorem isRelative_acceptAll (s : ChatStore) (rs : Array Rec) :
    (s.acceptAll rs).1.isRelative = s.isRelative := by
  cases s <;> rfl

/-- What `accept` says `accepted` for is stored: `d` is the record's digest, and the new store
holds it there. -/
theorem accept_accepted {s : ChatStore} {r : Rec} {d : Digest}
    (h : (s.accept r).1 = .accepted d) : d = hashRecord r ∧ (s.accept r).2.get d = some r := by
  cases s with
  | closed c =>
    have hraw : rawAccept c.raw r = (.accepted d, (c.accept r).2.raw) := Prod.ext h rfl
    obtain ⟨rfl, -, hmap, -⟩ := rawAccept_accepted hraw
    refine ⟨rfl, ?_⟩
    show (c.accept r).2.raw.map[hashRecord r]? = some r
    rw [hmap]
    exact Std.ExtTreeMap.getElem?_insert_self
  | relative c =>
    have hraw : rawAcceptRel c.raw c.boundary r = (.accepted d, (c.accept r).2.raw) :=
      Prod.ext h rfl
    obtain ⟨rfl, -, hmap, -⟩ := rawAcceptRel_accepted hraw
    refine ⟨rfl, ?_⟩
    show (c.accept r).2.raw.map[hashRecord r]? = some r
    rw [hmap]
    exact Std.ExtTreeMap.getElem?_insert_self

/-- `accept` says `accepted` for a record that is already stored, and changes nothing. -/
theorem accept_stored {s : ChatStore} {r : Rec} (h : s.get (hashRecord r) = some r) :
    (s.accept r).1 = .accepted (hashRecord r) := by
  have hb := s.builtRel
  have hg : r.group = s.raw.group := hb.group_eq _ r h
  have hw : r.WellSized := hb.wellSized _ r h
  have hl : ∀ x ∈ r.links, x ∈ s.raw.map ∨ x ∈ s.boundary := hb.closed _ r h
  have hc : ∀ old, s.raw.map[hashRecord r]? = some old → old = r := fun old ho => by
    simp only [get] at h
    rw [h] at ho
    exact (Option.some.inj ho).symm
  have hm : hashRecord r ∈ s.raw.map :=
    Std.ExtTreeMap.mem_iff_isSome_getElem?.mpr (by simp only [get] at h; simp [h])
  cases s with
  | closed c =>
    show (rawAccept c.raw r).1 = _
    rw [← rawAcceptRel_empty]
    exact rawAcceptRel_of_ok hg hw hl hc (fun hn => absurd hm hn)
  | relative c => exact rawAcceptRel_of_ok hg hw hl hc (fun hn => absurd hm hn)

/-- **What `acceptAll` guarantees, for either kind of store.** The kind, the chat and the boundary
are the same; every stored record is kept; every new record is from the batch; and `accept` on
the final store says `accepted` for a record of the batch only if it is stored there. -/
theorem acceptAll_sound (s : ChatStore) (rs : Array Rec) :
    (s.acceptAll rs).1.isRelative = s.isRelative ∧ (s.acceptAll rs).1.group = s.group ∧
    (s.acceptAll rs).1.boundary = s.boundary ∧
    (∀ (k : Digest) (x : Rec), s.get k = some x → (s.acceptAll rs).1.get k = some x) ∧
    (∀ (k : Digest) (x : Rec), (s.acceptAll rs).1.get k = some x → s.get k = some x ∨ x ∈ rs) ∧
    (∀ x ∈ rs, ∀ d, ((s.acceptAll rs).1.accept x).1 = .accepted d →
      (s.acceptAll rs).1.get d = some x) := by
  cases s with
  | closed c =>
    obtain ⟨hg, hk, ho, hst, -⟩ := CheckedStore.acceptAll_sound c rs
    have hstuck := CheckedStore.acceptAll_stuck c rs
    refine ⟨rfl, hg, rfl, hk, ho, fun x hx d hd => ?_⟩
    have hraw : rawAccept (c.acceptAll rs).1.raw x =
        (.accepted d, ((c.acceptAll rs).1.accept x).2.raw) := Prod.ext hd rfl
    obtain ⟨rfl, -⟩ := rawAccept_accepted hraw
    by_cases hl : x ∈ (c.acceptAll rs).2
    · exact absurd hd (hstuck x hl _)
    · exact hst x hx hl
  | relative c =>
    obtain ⟨hg, hb, hk, ho, -⟩ := RelStore.acceptAll_sound c rs
    exact ⟨rfl, hg, hb, hk, ho, fun x hx d hd => (RelStore.acceptAll_accepted hx hd).2⟩

/-- `accept`'s answer is `rawAcceptRel`'s on the store's data and boundary, for either kind. -/
theorem accept_fst (s : ChatStore) (r : Rec) :
    (s.accept r).1 = (rawAcceptRel s.raw s.boundary r).1 := by
  cases s with
  | closed c => exact (congrArg Prod.fst (rawAcceptRel_empty c.raw r)).symm
  | relative c => rfl

/-- **A larger boundary keeps `accepted`.** Two stores with the same records and chat, the
second's boundary holding every digest of the first's: if `accept` says `accepted d` on the
first, it does on the second. -/
theorem accept_fst_mono {s s' : ChatStore} {r : Rec} {d : Digest}
    (hm : s'.raw.map = s.raw.map) (hg : s'.raw.group = s.raw.group)
    (hB : ∀ x ∈ s'.boundary, x ∈ s.boundary) (h : (s'.accept r).1 = .accepted d) :
    (s.accept r).1 = .accepted d := by
  rw [accept_fst] at h ⊢
  exact rawAcceptRel_fst_mono hm hg hB h

/-- Drop the boundary digests that are not in `old`, stored nowhere, and linked by no stored
record (`RelStore.prune`). A closed store has no boundary and is unchanged. -/
def prune : ChatStore → Boundary → ChatStore
  | .closed c, _ => .closed c
  | .relative c, old => .relative (c.prune old)

/-- **What `prune` does, for either kind of store.** The kind, the records and the chat are the
same; the boundary only shrinks; a boundary digest that stays is in `old`, stored, or linked by a
stored record. -/
theorem prune_spec (s : ChatStore) (old : Boundary) :
    (s.prune old).isRelative = s.isRelative ∧ (s.prune old).raw.map = s.raw.map ∧
    (s.prune old).raw.group = s.raw.group ∧
    (∀ (x : Digest) (a : Aci), (s.prune old).boundary[x]? = some a → s.boundary[x]? = some a) ∧
    (∀ x, x ∈ (s.prune old).boundary → x ∈ old ∨ x ∈ s.raw.map ∨
      ∃ (k : Digest) (r : Rec), s.raw.map[k]? = some r ∧ x ∈ r.links) := by
  cases s with
  | closed c =>
    refine ⟨rfl, rfl, rfl, fun _ _ h => h, fun x hx => ?_⟩
    simp [prune, boundary] at hx
  | relative c =>
    obtain ⟨hm, hg, hb, hk⟩ := c.prune_spec old
    exact ⟨rfl, hm, hg, hb, hk⟩

open Examples in
#guard ((ChatStore.relative relStore).prune ∅).boundaryDigests.toList == [hashRecord a1]

/-- `CLASSIFY`: `classify` on a closed store (exactly the code the theorems about `classify` are
about), `classifyRaw` on a relative one. -/
def classify (s : ChatStore) (facts : Array Fact) : Std.ExtTreeMap Digest Status compare :=
  match s with
  | .closed c => Zrdt.classify c facts
  | .relative c => classifyRaw c.raw facts

/-- `LINKABLE`: the heads a new record of this device may link. A closed store links every head
(`HEADS`, as A7); a relative store only heads that are stored records in `live`
(`RelStore.linkable_sub`). -/
def linkable (s : ChatStore) (live : DigestSet) : Array Digest :=
  match s with
  | .closed c => c.headsArray
  | .relative c => c.linkable live

/-- **`linkable_sub`, for either kind of store.** Every digest `LINKABLE` returns is a head: no
stored record links it. For a relative store it is also a stored record in `live`. -/
theorem linkable_sub {s : ChatStore} {live : DigestSet} {d : Digest} (h : d ∈ s.linkable live) :
    (∀ (k : Digest) (x : Rec), s.get k = some x → d ∉ x.links) ∧
      (s.isRelative = true → (∃ r, s.get d = some r) ∧ d ∈ live) := by
  cases s with
  | closed c =>
    have hh : d ∈ c.heads := by
      simpa [linkable, CheckedStore.headsArray, Std.ExtTreeSet.mem_toList] using h
    exact ⟨fun k x hk => ((c.built.heads_iff d).mp hh).2 k x hk, by simp [isRelative]⟩
  | relative c =>
    obtain ⟨hr, hl, hn⟩ := RelStore.linkable_sub (c := c) h
    exact ⟨hn, fun _ => ⟨hr, hl⟩⟩

end ChatStore

/-! ## The blob -/

/-- The 6-byte tag that starts every `zrdtS3` blob. -/
def blob3Tag : ByteArray := "zrdtS3".toUTF8

example : blob3Tag.size = 6 := by decide

/-- The boundary section's entries, one after another: digest, then voucher. -/
def boundaryEntries : List (Digest × Aci) → ByteArray
  | [] => .empty
  | (d, a) :: rest => d.bytes ++ a.bytes ++ boundaryEntries rest

/-- The audience section's entries, one after another: digest, then the field-201 value as
`bytes`. -/
def audienceEntries : List (Digest × Array Serve.Seat) → ByteArray
  | [] => .empty
  | (d, a) :: rest =>
    d.bytes ++ u32be (Serve.writeAudience a).size ++ Serve.writeAudience a ++ audienceEntries rest

/-- Read `k` boundary entries from offset `off`. -/
def readBoundary (b : ByteArray) (off : Nat) : Nat → Option (List (Digest × Aci))
  | 0 => some []
  | k + 1 => do
    let d ← Digest.ofBytes? (b.extract off (off + 32))
    let a ← Aci.ofBytes? (b.extract (off + 32) (off + 48))
    let rest ← readBoundary b (off + 48) k
    pure ((d, a) :: rest)

/-- Read `k` audience entries from offset `off`: the entries and the offset after the last one.
Each value must be a well-formed audience (`Serve.parseAudience`). -/
def readAudiences (b : ByteArray) (off : Nat) :
    Nat → Option (List (Digest × Array Serve.Seat) × Nat)
  | 0 => some ([], off)
  | k + 1 => do
    let d ← Digest.ofBytes? (b.extract off (off + 32))
    let len ← readU32? b (off + 32)
    guard (off + 36 + len ≤ b.size)
    let a ← Serve.parseAudience (b.extract (off + 36) (off + 36 + len))
    let (rest, stop) ← readAudiences b (off + 36 + len) k
    pure ((d, a) :: rest, stop)

/-- What a `zrdtS3` blob holds, before any record is accepted. -/
structure Blob3 where
  /-- Mode 1: a relative store. -/
  relative : Bool
  /-- The boundary entries. -/
  boundary : List (Digest × Aci)
  /-- The audience entries. -/
  audiences : List (Digest × Array Serve.Seat)
  /-- The records, as a `zrdtS2` blob. -/
  records : ByteArray
deriving DecidableEq

/-- The mode byte: 0 closed, 1 relative. -/
def modeOf? (b : ByteArray) : Option Bool :=
  match b.data.toList with
  | [0] => some false
  | [1] => some true
  | _ => none

/-- The mode byte of a store reads back. -/
theorem modeOf?_byte (r : Bool) : modeOf? ⟨#[if r then 1 else 0]⟩ = some r := by
  cases r <;> rfl

/-- Decode the framing of a `zrdtS3` blob. `none` for a wrong tag or mode, a count the input
cannot hold, a closed blob with a boundary, an entry cut short or an audience that is not
well-formed. The records are decoded later, by `OPEN`'s loader. -/
def decodeChat (b : ByteArray) : Option Blob3 := do
  guard (b.extract 0 6 = blob3Tag)
  let relative ← modeOf? (b.extract 6 7)
  let n ← readU32? b 7
  guard (n < maxRecords ∧ 11 + 48 * n ≤ b.size ∧ (relative = true ∨ n = 0))
  let bnd ← readBoundary b 11 n
  let p := 11 + 48 * n
  let m ← readU32? b p
  guard (p + 4 + 36 * m ≤ b.size)
  let (auds, q) ← readAudiences b (p + 4) m
  guard (q ≤ b.size)
  pure ⟨relative, bnd, auds, b.extract q b.size⟩

/-- The audiences of stored records only, and only well-formed ones: what a blob carries. Every
audience `zrdtd` records is well-formed (`Serve.audienceOf_valid`, `Serve.valid_of_parseAudience`),
so the second test drops nothing; it makes `ChatStore.encode_reopens` hold for every table. -/
def storedAudiences (s : ChatStore) (auds : AudTable) : AudTable :=
  auds.filter fun d a => s.has d && Serve.validAudience a

/-- The `zrdtS3` blob of a chat's store and its audience table (`ENCODE`). Only audiences of
stored records are written. -/
def encodeChat (s : ChatStore) (auds : AudTable) : ByteArray :=
  let bnd := s.boundary.toList
  let as := (storedAudiences s auds).toList
  blob3Tag ++ ⟨#[if s.isRelative then 1 else 0]⟩ ++ u32be bnd.length ++ boundaryEntries bnd ++
    u32be as.length ++ audienceEntries as ++ s.inner

/-! ## Opening a blob -/

/-- Load the store of a decoded blob as a store of chat `g`: a closed blob with
`CheckedStore.open` (every check of `OPEN` before), a relative one with `RelStore.load` over its
boundary. -/
def openStore (g : GroupId) (x : Blob3) : Except OpenError ChatStore :=
  if blobTooLarge x.records then .error .tooLarge
  else if x.relative then
    match decodeBlob x.records with
    | none => .error .malformed
    | some (g', u) =>
      if g' ≠ g then .error .wrongChat
      else .relative <$> RelStore.load g (Std.ExtTreeMap.ofList x.boundary compare) u
  else .closed <$> CheckedStore.open g x.records

/-- Open a `zrdtS3` blob as the store of chat `g` (`OPEN`), with its audience table (kept for
stored records only). -/
def openChat (g : GroupId) (b : ByteArray) : Except OpenError (ChatStore × AudTable) :=
  match decodeChat b with
  | none => .error .malformed
  | some x => (fun s => (s, storedAudiences s (Std.ExtTreeMap.ofList x.audiences compare))) <$>
      openStore g x

/-- What `SALVAGE` loaded: the store of the records that could be accepted, the digests of the
records dropped, the digests they lack, and the blob's audiences of stored records. -/
structure ChatSalvaged where
  /-- The accepted records (over the blob's boundary, for a relative blob). -/
  store : ChatStore
  /-- The digests of the records that were not accepted, sorted. -/
  dropped : Array Digest
  /-- The link digests of the dropped records that point to nothing, sorted. -/
  missing : Array Digest
  /-- The audiences of stored records. -/
  audiences : AudTable

/-- `SALVAGE` of a `zrdtS3` blob: `CheckedStore.salvage` for a closed blob, `RelStore.salvage`
over its boundary for a relative one. -/
def salvageChat (g : GroupId) (b : ByteArray) : Except OpenError ChatSalvaged :=
  match decodeChat b with
  | none => .error .malformed
  | some x =>
    let finish (s : ChatStore) (dropped missing : Array Digest) : ChatSalvaged :=
      ⟨s, dropped, missing, storedAudiences s (Std.ExtTreeMap.ofList x.audiences compare)⟩
    if blobTooLarge x.records then .error .tooLarge
    else if x.relative then
      match decodeBlob x.records with
      | none => .error .malformed
      | some (g', u) =>
        if g' ≠ g then .error .wrongChat
        else
          match RelStore.salvage g (Std.ExtTreeMap.ofList x.boundary compare) u with
          | .ok sv => .ok (finish (.relative sv.store) sv.dropped sv.missing)
          | .error e => .error e
    else
      match CheckedStore.salvage g x.records with
      | .ok sv => .ok (finish (.closed sv.store) sv.dropped sv.missing)
      | .error e => .error e

/-- `MERGE` of a `zrdtS3` blob into a chat's store: the merged store, and the blob's audience
table. A closed store merges the blob's records with `CheckedStore.mergeBlob` (a relative blob's
records that link its boundary then fail: a closed store takes no boundary digest). A relative
store opens the blob as a store of its chat and adds its records and boundary (`RelStore.merge`).
`Zrdt.Proto` records the blob's audiences with `mergeAudiences`. -/
def mergeChat (s : ChatStore) (b : ByteArray) : Except OpenError (ChatStore × AudTable) :=
  match s with
  | .closed c =>
    match decodeChat b with
    | none => .error .malformed
    | some x =>
      if blobTooLarge x.records then .error .tooLarge
      else (fun c' => (.closed c', Std.ExtTreeMap.ofList x.audiences compare)) <$>
        c.mergeBlob x.records
  | .relative c =>
    match openChat c.group b with
    | .error e => .error e
    | .ok (d, auds) => (fun c' => (.relative c', auds)) <$> c.merge d.toRel

/-- The audiences after `MERGE` into the merged store `s`: every recorded audience stays, and the
blob's audience of a record stored in `s` is added where none is recorded. -/
def mergeAudiences (s : ChatStore) (auds blobAuds : AudTable) : AudTable :=
  blobAuds.foldl (init := auds) fun m d a => if s.has d && !m.contains d then m.insert d a else m

/-- **What `mergeAudiences` records.** Every recorded audience stays. An audience in the result
was recorded before, or it is the blob's audience of a record stored in `s` that had none. -/
theorem mergeAudiences_spec (s : ChatStore) (auds blobAuds : AudTable) :
    (∀ (d : Digest) (a : Array Serve.Seat), auds[d]? = some a →
      (mergeAudiences s auds blobAuds)[d]? = some a) ∧
    (∀ (d : Digest) (a : Array Serve.Seat), (mergeAudiences s auds blobAuds)[d]? = some a →
      auds[d]? = some a ∨ (auds[d]? = none ∧ s.has d = true ∧ blobAuds[d]? = some a)) := by
  have step : ∀ (l : List (Digest × Array Serve.Seat)) (m : AudTable),
      (∀ x ∈ l, blobAuds[x.1]? = some x.2) →
      (∀ (d : Digest) (a : Array Serve.Seat), m[d]? = some a →
        (l.foldl (fun (m : AudTable) p => if s.has p.1 && !m.contains p.1 then m.insert p.1 p.2
          else m) m)[d]? = some a) ∧
      (∀ (d : Digest) (a : Array Serve.Seat), (l.foldl (fun (m : AudTable) p =>
          if s.has p.1 && !m.contains p.1 then m.insert p.1 p.2 else m) m)[d]? = some a →
        m[d]? = some a ∨ (m[d]? = none ∧ s.has d = true ∧ blobAuds[d]? = some a)) := by
    intro l
    induction l with
    | nil => intro m _; exact ⟨fun _ _ h => h, fun _ _ h => .inl h⟩
    | cons p rest ih =>
      intro m hl
      obtain ⟨keep, only⟩ := ih (if s.has p.1 && !m.contains p.1 then m.insert p.1 p.2 else m)
        fun x hx => hl x (List.mem_cons_of_mem _ hx)
      have hp := hl p List.mem_cons_self
      simp only [List.foldl_cons]
      refine ⟨fun d a hd => keep d a ?_, fun d a hd => ?_⟩
      · split
        · rename_i hc
          simp only [Bool.and_eq_true, Bool.not_eq_true'] at hc
          rw [Std.ExtTreeMap.getElem?_insert]
          split
          · rename_i he
            rw [Std.LawfulEqCmp.compare_eq_iff_eq] at he
            subst he
            rw [Std.ExtTreeMap.contains_eq_isSome_getElem?, hd] at hc
            cases hc.2
          · exact hd
        · exact hd
      · rcases only d a hd with h | ⟨hn, hs, hb⟩
        · split at h
          · rename_i hc
            simp only [Bool.and_eq_true, Bool.not_eq_true'] at hc
            rw [Std.ExtTreeMap.getElem?_insert] at h
            split at h
            · rename_i he
              rw [Std.LawfulEqCmp.compare_eq_iff_eq] at he
              subst he
              cases h
              refine .inr ⟨?_, hc.1, hp⟩
              rw [Std.ExtTreeMap.contains_eq_isSome_getElem?] at hc
              cases hm : m[p.1]? with
              | none => rfl
              | some _ => rw [hm] at hc; cases hc.2
            · exact .inl h
          · exact .inl h
        · split at hn
          · rw [Std.ExtTreeMap.getElem?_insert] at hn
            split at hn
            · cases hn
            · exact .inr ⟨hn, hs, hb⟩
          · exact .inr ⟨hn, hs, hb⟩
  have := step blobAuds.toList auds fun x hx =>
    Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some.mp hx
  rw [mergeAudiences, Std.ExtTreeMap.foldl_eq_foldl_toList]
  exact this

/-! ## Reading back what was written -/

section Proofs
open Encode

@[simp] theorem size_blob3Tag : blob3Tag.size = 6 := by decide

theorem size_boundaryEntries (l : List (Digest × Aci)) :
    (boundaryEntries l).size = 48 * l.length := by
  induction l with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨d, a⟩ := p
    simp [boundaryEntries, ByteArray.size_append, ih, d.size_eq, a.size_eq]
    omega

/-- `readBoundary` reads back entries written by `boundaryEntries`. -/
theorem readBoundary_entries (l : List (Digest × Aci)) (p s : ByteArray) :
    readBoundary (p ++ (boundaryEntries l ++ s)) p.size l.length = some l := by
  induction l generalizing p with
  | nil => rfl
  | cons x rest ih =>
    obtain ⟨d, a⟩ := x
    have hd : (p ++ (boundaryEntries ((d, a) :: rest) ++ s)).extract p.size (p.size + 32) =
        d.bytes := by
      simp only [boundaryEntries, ByteArray.append_assoc]
      exact extract_append_mid rfl (by rw [d.size_eq])
    have ha : (p ++ (boundaryEntries ((d, a) :: rest) ++ s)).extract (p.size + 32)
        (p.size + 48) = a.bytes := by
      have : p ++ (boundaryEntries ((d, a) :: rest) ++ s) =
          (p ++ d.bytes) ++ (a.bytes ++ (boundaryEntries rest ++ s)) := by
        simp [boundaryEntries, ByteArray.append_assoc]
      rw [this]
      exact extract_append_mid (by simp [ByteArray.size_append, d.size_eq])
        (by simp [ByteArray.size_append, d.size_eq, a.size_eq])
    have hr : p ++ (boundaryEntries ((d, a) :: rest) ++ s) =
        (p ++ d.bytes ++ a.bytes) ++ (boundaryEntries rest ++ s) := by
      simp [boundaryEntries, ByteArray.append_assoc]
    have hsz : (p ++ d.bytes ++ a.bytes).size = p.size + 48 := by
      simp [ByteArray.size_append, d.size_eq, a.size_eq]
    simp only [List.length_cons, readBoundary, hd, ha, Digest.ofBytes?_bytes, Aci.ofBytes?_bytes,
      Option.bind_eq_bind, Option.bind_some]
    rw [hr, ← hsz, ih]
    rfl

/-- A well-formed audience value is at most `32 * maxAudience` bytes. -/
theorem size_of_parseAudience {b : ByteArray} {a : Array Serve.Seat}
    (h : Serve.parseAudience b = some a) : b.size ≤ 32 * Serve.maxAudience := by
  unfold Serve.parseAudience at h
  simp only [guard, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨_, hg, _⟩ := h
  exact (Encode.guard_eq_some hg).2.2

theorem size_audienceEntries_ge (l : List (Digest × Array Serve.Seat)) :
    36 * l.length ≤ (audienceEntries l).size := by
  induction l with
  | nil => simp [audienceEntries]
  | cons x rest ih =>
    obtain ⟨d, a⟩ := x
    simp only [audienceEntries, ByteArray.size_append, size_u32be, d.size_eq,
      List.length_cons] at ih ⊢
    omega

/-- `readAudiences` reads back entries written by `audienceEntries`, when each audience reads
back through `parseAudience`. -/
theorem readAudiences_entries (l : List (Digest × Array Serve.Seat))
    (hl : ∀ x ∈ l, Serve.parseAudience (Serve.writeAudience x.2) = some x.2) (p s : ByteArray) :
    readAudiences (p ++ (audienceEntries l ++ s)) p.size l.length =
      some (l, p.size + (audienceEntries l).size) := by
  induction l generalizing p with
  | nil => simp [readAudiences, audienceEntries]
  | cons x rest ih =>
    obtain ⟨d, a⟩ := x
    have hpa := hl (d, a) List.mem_cons_self
    have hrest : ∀ x ∈ rest, Serve.parseAudience (Serve.writeAudience x.2) = some x.2 :=
      fun x hx => hl x (List.mem_cons_of_mem _ hx)
    have hlen : (Serve.writeAudience a).size < 2^32 := by
      have := size_of_parseAudience hpa
      simp only [Serve.maxAudience] at this
      omega
    let w := Serve.writeAudience a
    have hd : (p ++ (audienceEntries ((d, a) :: rest) ++ s)).extract p.size (p.size + 32) =
        d.bytes := by
      simp only [audienceEntries, ByteArray.append_assoc]
      exact extract_append_mid rfl (by rw [d.size_eq])
    have hu : readU32? (p ++ (audienceEntries ((d, a) :: rest) ++ s)) (p.size + 32) =
        some w.size := by
      rw [readU32?_of_extract (n := w.size), Nat.mod_eq_of_lt hlen]
      have : p ++ (audienceEntries ((d, a) :: rest) ++ s) =
          (p ++ d.bytes) ++ (u32be w.size ++ (w ++ (audienceEntries rest ++ s))) := by
        simp [audienceEntries, w, ByteArray.append_assoc]
      rw [this]
      exact extract_append_mid (by simp [ByteArray.size_append, d.size_eq])
        (by simp [ByteArray.size_append, d.size_eq])
    have hsz : (p ++ (audienceEntries ((d, a) :: rest) ++ s)).size =
        p.size + 36 + w.size + (audienceEntries rest).size + s.size := by
      simp [audienceEntries, w, ByteArray.size_append, d.size_eq]; omega
    have hw : (p ++ (audienceEntries ((d, a) :: rest) ++ s)).extract (p.size + 36)
        (p.size + 36 + w.size) = w := by
      have : p ++ (audienceEntries ((d, a) :: rest) ++ s) =
          (p ++ d.bytes ++ u32be w.size) ++ (w ++ (audienceEntries rest ++ s)) := by
        simp [audienceEntries, w, ByteArray.append_assoc]
      rw [this]
      exact extract_append_mid (by simp [ByteArray.size_append, d.size_eq])
        (by simp [ByteArray.size_append, d.size_eq])
    have hr : p ++ (audienceEntries ((d, a) :: rest) ++ s) =
        (p ++ d.bytes ++ u32be w.size ++ w) ++ (audienceEntries rest ++ s) := by
      simp [audienceEntries, w, ByteArray.append_assoc]
    have hpsz : (p ++ d.bytes ++ u32be w.size ++ w).size = p.size + 36 + w.size := by
      simp [ByteArray.size_append, d.size_eq]
    simp only [List.length_cons, readAudiences, hd, Digest.ofBytes?_bytes, Option.bind_eq_bind,
      Option.bind_some, hu]
    have hg : p.size + 32 + 4 + w.size ≤ (p ++ (audienceEntries ((d, a) :: rest) ++ s)).size := by
      rw [hsz]; omega
    simp only [show p.size + 32 + 4 = p.size + 36 by omega] at hg ⊢
    simp only [guard, hg, ↓reduceIte, Option.pure_def, Option.bind_some, hw]
    rw [show Serve.parseAudience w = some a from hpa]
    simp only [Option.bind_some]
    rw [hr, ← hpsz, ih hrest]
    simp only [Option.bind_some, Option.some.injEq, Prod.mk.injEq, true_and]
    simp [audienceEntries, w, ByteArray.size_append, d.size_eq]
    omega

/-- A map is the map of its own list. -/
theorem ofList_toList {β : Type} (t : Std.ExtTreeMap Digest β compare) :
    Std.ExtTreeMap.ofList t.toList compare = t := by
  apply Std.ExtTreeMap.ext_getElem?
  intro k
  cases hk : t[k]? with
  | some v =>
    exact Std.ExtTreeMap.getElem?_ofList_of_mem (k := k) (Std.ReflCmp.compare_self)
      Std.ExtTreeMap.distinct_keys_toList (Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some.mpr hk)
  | none =>
    apply Std.ExtTreeMap.getElem?_ofList_of_contains_eq_false
    rw [Bool.eq_false_iff]
    intro hc
    obtain ⟨⟨k', v⟩, hm, hk'⟩ := List.mem_map.mp (List.contains_iff_mem.mp hc)
    simp only at hk'
    subst hk'
    rw [Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some] at hm
    simp [hm] at hk

/-- Keeping the audiences of stored records twice is keeping them once. -/
theorem storedAudiences_idem (s : ChatStore) (auds : AudTable) :
    storedAudiences s (storedAudiences s auds) = storedAudiences s auds := by
  apply Std.ExtTreeMap.ext_getElem?
  intro k
  simp only [storedAudiences, Std.ExtTreeMap.getElem?_filter']
  cases auds[k]? <;> simp [Option.filter]
  split <;> simp_all

/-- The audiences a blob carries are fewer than `maxRecords`: one per stored record at most. -/
theorem size_storedAudiences (s : ChatStore) (auds : AudTable) :
    (storedAudiences s auds).size < maxRecords := by
  have hle : (storedAudiences s auds).size ≤ s.raw.map.size := by
    rw [← Std.ExtTreeMap.length_keys, ← Std.ExtTreeMap.length_keys]
    apply Std.ExtTreeMap.nodup_keys.length_le_of_subset
    intro k hk
    have hk' := Std.ExtTreeMap.mem_keys.mp hk
    rw [storedAudiences, Std.ExtTreeMap.mem_filter] at hk'
    obtain ⟨_, hhas⟩ := hk'
    simp only [ChatStore.has, Std.ExtTreeMap.getKey_eq, Bool.and_eq_true] at hhas
    exact Std.ExtTreeMap.mem_keys.mpr (Std.ExtTreeMap.mem_iff_contains.mpr hhas.1)
  have := s.builtRel.size_lt
  omega

/-- **The framing reads back.** A store's blob decodes to its mode, its boundary, its stored
audiences and its records blob. -/
theorem decodeChat_encodeChat (s : ChatStore) (auds : AudTable) :
    decodeChat (encodeChat s auds) =
      some ⟨s.isRelative, s.boundary.toList, (storedAudiences s auds).toList, s.inner⟩ := by
  let bnd := s.boundary.toList
  let as := (storedAudiences s auds).toList
  let mode : ByteArray := ⟨#[if s.isRelative then 1 else 0]⟩
  have hms : mode.size = 1 := rfl
  have hn : bnd.length < maxRecords := by
    simp only [bnd, Std.ExtTreeMap.length_toList]; exact s.builtRel.boundary_lt
  have hm : as.length < maxRecords := by
    simp only [as, Std.ExtTreeMap.length_toList]; exact size_storedAudiences s auds
  have hmax : maxRecords = 2^24 := rfl
  have hn32 : bnd.length < 2^32 := by omega
  have hm32 : as.length < 2^32 := by omega
  have has : ∀ x ∈ as, Serve.parseAudience (Serve.writeAudience x.2) = some x.2 := by
    intro x hx
    have := Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some.mp hx
    simp only [storedAudiences, Std.ExtTreeMap.getElem?_filter'] at this
    obtain ⟨-, hv⟩ := Option.filter_eq_some_iff.mp this
    simp only [Bool.and_eq_true] at hv
    exact Serve.parseAudience_writeAudience hv.2
  have hclosed : s.isRelative = true ∨ bnd.length = 0 := by
    cases s with
    | closed c => right; simp [bnd, ChatStore.boundary]
    | relative c => left; rfl
  -- The blob, cut at each section.
  have e0 : encodeChat s auds = blob3Tag ++ (mode ++ (u32be bnd.length ++ (boundaryEntries bnd ++
      (u32be as.length ++ (audienceEntries as ++ s.inner))))) := by
    simp [encodeChat, bnd, as, mode, ByteArray.append_assoc]
  have hsize : (encodeChat s auds).size = 11 + 48 * bnd.length + 4 + (audienceEntries as).size +
      s.inner.size := by
    rw [e0]; simp [ByteArray.size_append, hms, size_boundaryEntries]; omega
  have htag : (encodeChat s auds).extract 0 6 = blob3Tag := by
    rw [e0]; exact ByteArray.extract_append_eq_left (by simp)
  have hmode : (encodeChat s auds).extract 6 7 = mode := by
    rw [e0]
    exact extract_append_mid (by simp) (by simp [hms])
  have hrel : modeOf? mode = some s.isRelative := modeOf?_byte _
  have hu1 : readU32? (encodeChat s auds) 7 = some bnd.length := by
    rw [readU32?_of_extract (n := bnd.length), Nat.mod_eq_of_lt hn32]
    have : encodeChat s auds = (blob3Tag ++ mode) ++ (u32be bnd.length ++ (boundaryEntries bnd ++
        (u32be as.length ++ (audienceEntries as ++ s.inner)))) := by
      rw [e0]; simp [ByteArray.append_assoc]
    rw [this]
    exact extract_append_mid (by simp [ByteArray.size_append, hms])
      (by simp [ByteArray.size_append, hms])
  have hb : readBoundary (encodeChat s auds) 11 bnd.length = some bnd := by
    have : encodeChat s auds = (blob3Tag ++ mode ++ u32be bnd.length) ++ (boundaryEntries bnd ++
        (u32be as.length ++ (audienceEntries as ++ s.inner))) := by
      rw [e0]; simp [ByteArray.append_assoc]
    have h11 : (blob3Tag ++ mode ++ u32be bnd.length).size = 11 := by
      simp [ByteArray.size_append, hms]
    rw [this, ← h11]
    exact readBoundary_entries bnd _ _
  have hu2 : readU32? (encodeChat s auds) (11 + 48 * bnd.length) = some as.length := by
    rw [readU32?_of_extract (n := as.length), Nat.mod_eq_of_lt hm32]
    have : encodeChat s auds = (blob3Tag ++ mode ++ u32be bnd.length ++ boundaryEntries bnd) ++
        (u32be as.length ++ (audienceEntries as ++ s.inner)) := by
      rw [e0]; simp [ByteArray.append_assoc]
    rw [this]
    exact extract_append_mid (by simp [ByteArray.size_append, hms, size_boundaryEntries])
      (by simp [ByteArray.size_append, hms, size_boundaryEntries])
  have ha : readAudiences (encodeChat s auds) (11 + 48 * bnd.length + 4) as.length =
      some (as, 11 + 48 * bnd.length + 4 + (audienceEntries as).size) := by
    have : encodeChat s auds = (blob3Tag ++ mode ++ u32be bnd.length ++ boundaryEntries bnd ++
        u32be as.length) ++ (audienceEntries as ++ s.inner) := by
      rw [e0]; simp [ByteArray.append_assoc]
    have hp' : (blob3Tag ++ mode ++ u32be bnd.length ++ boundaryEntries bnd ++
        u32be as.length).size = 11 + 48 * bnd.length + 4 := by
      simp [ByteArray.size_append, hms, size_boundaryEntries]
    rw [this, ← hp']
    exact readAudiences_entries as has _ _
  have hinner : (encodeChat s auds).extract (11 + 48 * bnd.length + 4 + (audienceEntries as).size)
      (encodeChat s auds).size = s.inner := by
    have : encodeChat s auds = (blob3Tag ++ mode ++ u32be bnd.length ++ boundaryEntries bnd ++
        u32be as.length ++ audienceEntries as) ++ (s.inner ++ ByteArray.empty) := by
      rw [e0]; simp [ByteArray.append_assoc, ByteArray.append_empty]
    rw [hsize, this]
    exact extract_append_mid (by simp [ByteArray.size_append, hms, size_boundaryEntries])
      (by simp [ByteArray.size_append, hms, size_boundaryEntries])
  have hge := size_audienceEntries_ge as
  have h1 : 11 + 48 * bnd.length ≤ (encodeChat s auds).size := by rw [hsize]; omega
  have h2 : 11 + 48 * bnd.length + 4 + 36 * as.length ≤ (encodeChat s auds).size := by
    rw [hsize]; omega
  have h3 : 11 + 48 * bnd.length + 4 + (audienceEntries as).size ≤ (encodeChat s auds).size := by
    rw [hsize]; omega
  unfold decodeChat
  simp only [htag, guard, ↓reduceIte, Option.pure_def, Option.bind_eq_bind, Option.bind_some,
    hmode, hrel, hu1, hn, h1, hclosed, and_self, hb, hu2, h2, ha, h3, hinner]
  rfl

/-- A blob whose count is too large does not decode. -/
theorem decodeBlob_of_blobTooLarge {b : ByteArray} (h : blobTooLarge b = true) :
    decodeBlob b = none := by
  simp only [blobTooLarge, Bool.and_eq_true, Option.any_eq_true, decide_eq_true_eq] at h
  obtain ⟨-, n, hn, hle⟩ := h
  rw [Option.eq_none_iff_forall_ne_some]
  intro x hx
  simp only [decodeBlob, guard, Option.bind_eq_bind, Option.pure_def,
    Option.bind_eq_some_iff] at hx
  obtain ⟨_, _, _, _, _, _, count, hcount, _, hlt, _⟩ := hx
  have hlt := guard_eq_some hlt
  rw [hn] at hcount
  cases hcount
  omega

/-- The records of a correct store are within the size limits. -/
theorem wellSized_values {c : RawStore} {B : Boundary} (h : BuiltRel c B) :
    WellSized (c.map.toList.map Prod.snd).toArray := by
  refine ⟨?_, fun r hr => ?_⟩
  · simp only [List.size_toArray, List.length_map, Std.ExtTreeMap.length_toList]
    exact h.size_lt
  · simp only [List.mem_toArray, List.mem_map] at hr
    obtain ⟨⟨k, x⟩, hk, rfl⟩ := hr
    exact h.wellSized k x (Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some.mp hk)

/-- The store of a blob reloads as itself. -/
theorem openStore_encode (s : ChatStore) (l : List (Digest × Array Serve.Seat)) :
    openStore s.group ⟨s.isRelative, s.boundary.toList, l, s.inner⟩ = .ok s := by
  cases s with
  | closed c =>
    have hws : WellSized c.records := wellSized_values (builtRel_empty_iff.mpr c.built)
    have hnot : blobTooLarge c.encode = false := by
      rw [Bool.eq_false_iff]
      intro ht
      have := decodeBlob_of_blobTooLarge ht
      rw [CheckedStore.encode, decodeBlob_encodeBlob _ _ hws] at this
      cases this
    simp only [openStore, ChatStore.inner, hnot, ChatStore.isRelative, Bool.false_eq_true,
      ↓reduceIte]
    show ChatStore.closed <$> CheckedStore.open c.group c.encode = _
    rw [CheckedStore.encode_reopens]
    rfl
  | relative c =>
    have hws : WellSized c.records := wellSized_values c.built
    have hdec : decodeBlob (encodeBlob c.group c.records) = some (c.group, c.records) :=
      decodeBlob_encodeBlob _ _ hws
    have hnot : blobTooLarge (encodeBlob c.group c.records) = false := by
      rw [Bool.eq_false_iff]
      intro ht
      rw [decodeBlob_of_blobTooLarge ht] at hdec
      cases hdec
    simp only [openStore, ChatStore.inner, hnot, ChatStore.isRelative, ↓reduceIte, hdec]
    simp only [ne_eq, ChatStore.boundary, ofList_toList]
    show (if c.group ≠ c.group then _ else ChatStore.relative <$>
      RelStore.load c.group c.boundary c.records) = _
    rw [RelStore.load_reopens]
    simp
    rfl

/-- **A chat's blob reopens as itself:** opening the blob of a store and its audience table,
under its own chat, gives back exactly that store (records, heads, boundary and vouchers) and the
audiences of its stored records (`storedAudiences`: every one `zrdtd` records, since each is
well-formed and reads back, `Serve.parseAudience_writeAudience`). -/
theorem ChatStore.encode_reopens (s : ChatStore) (auds : AudTable) :
    openChat s.group (encodeChat s auds) = .ok (s, storedAudiences s auds) := by
  unfold openChat
  rw [decodeChat_encodeChat s auds]
  simp only
  rw [openStore_encode]
  simp only [Functor.map, Except.map, ofList_toList, storedAudiences_idem]

end Proofs

/-! ## Examples -/

open Examples

-- A relative store's blob reopens: same heads, same boundary digest, relative.
#guard match openChat group (encodeChat (.relative relStore) ∅) with
  | .ok (s, auds) => s.headsArray == relStore.headsArray && s.isRelative &&
    s.boundaryDigests.toList == [hashRecord a1] && auds.isEmpty
  | .error _ => false
-- A closed store's blob reopens closed; an audience of a stored record is kept, one of a record
-- that is not stored is not written.
#guard match openChat group (encodeChat (.closed all4) ((∅ : AudTable).insert (hashRecord a1)
    #[⟨alice, Serve.keyTag ⟨#[1]⟩⟩] |>.insert (dig 9) #[⟨alice, Serve.zeroTag⟩])) with
  | .ok (s, auds) => s.headsArray == all4.headsArray && !s.isRelative &&
    auds.toList == [(hashRecord a1, #[⟨alice, Serve.keyTag ⟨#[1]⟩⟩])]
  | .error _ => false
-- The audiences `ACCEPT` records are well-formed and read back.
#guard (Serve.audienceOf Serve.Examples.welcome.2).all fun a =>
  Serve.validAudience a && Serve.parseAudience (Serve.writeAudience a) == some a
-- Refused: a closed blob that lists a boundary digest; a `zrdtS2` blob; another chat.
#guard (decodeChat (blob3Tag ++ ⟨#[0]⟩ ++ u32be 1 ++ (hashRecord a1).bytes ++ alice.bytes ++
  u32be 0 ++ all4.encode)).isNone
#guard (decodeChat all4.encode).isNone
#guard match openChat otherGroup (encodeChat (.closed all4) ∅) with
  | .error .wrongChat => true
  | _ => false
-- `SALVAGE` of the relative blob without its boundary keeps nothing; `MERGE` of a closed store's
-- blob into the relative store promotes nothing it lacks and adds `a1`'s record.
#guard match salvageChat group (encodeChat (.relative relStore) ∅) with
  | .ok sv => sv.store.isRelative && sv.dropped.size == 0
  | .error _ => false
#guard match mergeChat (.relative relStore) (encodeChat (.closed all4) ∅) with
  | .ok (s, _) => s.has (hashRecord a1) && s.headsArray == all4.headsArray
  | .error _ => false
-- A closed store refuses a relative blob's records that need its boundary.
#guard match mergeChat (.closed (CheckedStore.empty group)) (encodeChat (.relative relStore) ∅) with
  | .error (.unverifiable _ m) => m == #[hashRecord a1]
  | _ => false

-- The guarantee on a concrete store.
example : openChat (ChatStore.relative relStore).group (encodeChat (.relative relStore) ∅) =
    .ok (.relative relStore, storedAudiences (.relative relStore) ∅) :=
  ChatStore.encode_reopens _ _

end Zrdt
