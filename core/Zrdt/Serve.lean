import Zrdt.Commit
import Zrdt.Store

/-!
# `SERVE`: what a member sends another member about its store (docs/JOIN_PLAN.md §3, §5, §7.1)

**The audience.** Every record message carries its author's audience in `DataMessage` field 201
(`zrdtAudience`): 1 to 256 entries `aci (16) ‖ keyTag (16)`, strictly increasing by ACI. The key
tag is the first 16 bytes of SHA-256(`"zrdtK1"` ‖ the 33-byte identity public key the author held
for that member when it froze the message), or 16 zero bytes for a member Signal does not send
the message to (blocked, seen as unregistered, or no key). Field 201 is not field 15 or 200, so it
is in the committed bytes: a matching opening carries the audience its author committed to
(`audience_bound`). The project is greenfield: every record message has field 201. An opening
without one is refused when it is stored (`Zrdt.Proto`, `NO_AUDIENCE`), and `serve` never sends
the content of a message without one.

**Seated.** `seats aud aci key`: the audience has an entry with that ACI and the tag of that key,
and the tag is not zero. There is no author shortcut: the author is seated by its own entry,
under its own key.

**`serve c me held q`** answers requester `q` from a responder with store `c`, own state `me`
(its ACI, the digests it holds `live`, its disown set, and its own boundary digests, empty for a
closed store) and what it holds outside the store for each record (`held`: the opening, and the
audience `zrdtd` recorded from an opening it checked earlier). The reply is a list of entries,
one per stored record or boundary digest at most:

- `addressed r o ac`: `q` is seated in the audience the responder knows for `r`, and (catch-up)
  `r` is not reachable from `q`'s `since`, or (per-digest) `r` was asked for. `o` is the opening,
  sent only if it matches `r.commit`, **its own committed audience seats `q`**, it is not
  disappearing or view-once in an export, and, in strict mode, `ac` holds. `ac` (author copy):
  the responder wrote `r`, holds it `live`, and has not disowned it.
- `after r`: `r` reaches a record of the first kind (the walk back from them, `upSet`). Its
  structure, never its content.
- `boundary d`: a stored record that is neither, or a digest of the responder's own boundary,
  that a served record links or that is a head (per-digest: any wanted digest). The digest only.
- nothing, otherwise.

`since` is the requester's `since` joined with the responder's own `since` for that account
(`Query.since`, `Query.ownSince`). It shapes structure, never content: a per-digest request gets
the content of a wanted record whatever `since` says.

**Proved here.** `serve_content`: every opening in a reply opens a stored record, and its own
committed audience seats the requester's ACI with the tag of the requester's key. It does not
mention the audience cache, `since`, the strict flag or any provenance, so no stale cache or host
mistake can widen it. `serve_content_complete`: the converse; every held opening that
`serveOpening` accepts is in the reply. `serve_authorCopy`, `serve_strict`, `serve_export`,
`serve_after`, `serve_boundary`, `serveOpening_spec`, `audience_bound`.

**Trusted** (JOIN_PLAN §9): the protobuf scan of field 201 (`fieldValue`, `audienceOf`), as for
the commitment's scan; the key `q.key` is the one Desktop holds for the requester (TOFU), and the
host seals the reply to exactly that key (`Zrdt.Proto.run_serve_content` ties the reply header's
tag to it).
-/

namespace Zrdt
namespace Serve

/-! ## The audience (field 201) -/

/-- The `DataMessage` field that carries the audience. -/
def audienceField : Nat := 201

/-- The most entries an audience may have (JOIN_PLAN §12.2, decided: 256). -/
def maxAudience : Nat := 256

/-- One audience entry: an account, and the tag of the identity key the author held for it
(`zeroTag` for a member the message is not sent to). -/
structure Seat where
  /-- The member's account id. -/
  aci : Aci
  /-- 16 bytes: `keyTag` of the member's identity key, or `zeroTag`. -/
  tag : Array UInt8
deriving DecidableEq, Repr

/-- The tag of a member Signal does not send the message to (blocked, seen as unregistered, or no
key). It seats nobody. -/
def zeroTag : Array UInt8 := Array.replicate 16 0

/-- The tag of an identity key (33 bytes serialized): the first 16 bytes of
SHA-256(`"zrdtK1"` ‖ key). A hash of a public key, so it signs nothing. -/
def keyTag (key : ByteArray) : Array UInt8 :=
  ((sha256 ("zrdtK1".toUTF8 ++ key)).bytes.extract 0 16).data

#guard (keyTag ⟨Array.replicate 33 1⟩).size == 16
#guard keyTag ⟨Array.replicate 33 1⟩ != keyTag ⟨Array.replicate 33 2⟩

/-- The value bytes of field `f` of message `m`, if `f` is length-delimited (wire type 2). -/
def fieldValue (m : ByteArray) (f : Field) : Option ByteArray := do
  let (key, p) ← readVarint m f.start
  guard (key &&& 7 = 2)
  let (len, q) ← readVarint m p
  guard (q + len ≤ m.size)
  pure (m.extract q (q + len))

/-- The value of field `f` of message `m`, if `f` is a varint (wire type 0). -/
def varintValue (m : ByteArray) (f : Field) : Option Nat := do
  let (key, p) ← readVarint m f.start
  guard (key &&& 7 = 0)
  let (v, _) ← readVarint m p
  pure v

open Examples in
#guard ((fields bodyField).bind (·[0]?)).bind (fieldValue bodyField) == some "hello".toUTF8
open Examples in
#guard ((fields timestampField).bind (·[0]?)).bind (varintValue timestampField) ==
  some 1730419200000

/-- The entries of a field-201 value: 1 to `maxAudience` entries `aci (16) ‖ tag (16)`, strictly
increasing by ACI. `none` for anything else. -/
def parseAudience (b : ByteArray) : Option (Array Seat) := do
  guard (b.size % 32 = 0 ∧ 32 ≤ b.size ∧ b.size ≤ 32 * maxAudience)
  let seats ← (List.range (b.size / 32)).toArray.mapM fun i => do
    let a ← Aci.ofBytes? (b.extract (32 * i) (32 * i + 16))
    pure ({ aci := a, tag := (b.extract (32 * i + 16) (32 * i + 32)).data } : Seat)
  guard ((seats.toList.zip seats.toList.tail).all fun (x, y) => compare x.aci y.aci == .lt)
  pure seats

/-- The field-201 value of `seats`: the entries one after the other. The inverse of
`parseAudience` on a well-formed audience. -/
def writeAudience (seats : Array Seat) : ByteArray :=
  seats.foldl (fun b s => b ++ s.aci.bytes ++ ⟨s.tag⟩) .empty

open Examples in
#guard parseAudience (writeAudience #[⟨alice, keyTag ⟨#[1]⟩⟩, ⟨bob, zeroTag⟩]) ==
  some #[⟨alice, keyTag ⟨#[1]⟩⟩, ⟨bob, zeroTag⟩]
open Examples in
-- Out of order, repeated, empty, and a cut entry are all refused.
#guard [writeAudience #[⟨bob, zeroTag⟩, ⟨alice, zeroTag⟩],
  writeAudience #[⟨alice, zeroTag⟩, ⟨alice, zeroTag⟩], .empty,
  (writeAudience #[⟨alice, zeroTag⟩]).extract 0 31].all (parseAudience · == none)
-- 256 entries are allowed, 257 are not.
#guard (parseAudience (writeAudience ((List.range 256).toArray.map fun i =>
  ⟨⟨⟨Array.replicate 14 0 ++ #[(i / 256).toUInt8, (i % 256).toUInt8]⟩, rfl⟩, zeroTag⟩))).isSome
#guard (parseAudience (writeAudience ((List.range 257).toArray.map fun i =>
  ⟨⟨⟨Array.replicate 14 0 ++ #[(i / 256).toUInt8, (i % 256).toUInt8]⟩, rfl⟩, zeroTag⟩))).isNone

/-- The audience committed in an opening: its committed bytes hold exactly one field 201, and its
value is a well-formed audience. `none` otherwise (no field 201, two of them, or a bad value). -/
def audienceOf (o : ByteArray) : Option (Array Seat) := do
  let (_, m) ← splitOpening o
  let fs ← fields m
  match (fs.filter (·.num == audienceField)).toList with
  | [f] => parseAudience (← fieldValue m f)
  | _ => none

/-- `aud` seats the account `aci` whose identity key, as this device holds it, is `key`: an entry
with that ACI and that key's tag, and the tag is not zero. -/
def seats (aud : Array Seat) (aci : Aci) (key : ByteArray) : Bool :=
  aud.any fun s => s.aci == aci && s.tag == keyTag key && s.tag != zeroTag

open Examples in
#guard seats #[⟨alice, keyTag ⟨#[1]⟩⟩, ⟨bob, zeroTag⟩] alice ⟨#[1]⟩ &&
  !seats #[⟨alice, keyTag ⟨#[1]⟩⟩, ⟨bob, zeroTag⟩] alice ⟨#[2]⟩ &&
  !seats #[⟨alice, keyTag ⟨#[1]⟩⟩, ⟨bob, zeroTag⟩] bob ⟨#[1]⟩

/-- The committed message disappears or is view-once: a top-level field 5 (`expireTimer`) or 14
(`isViewOnce`) is non-zero. Anything that cannot be read counts as ephemeral. -/
def ephemeral (o : ByteArray) : Bool :=
  match splitOpening o with
  | none => true
  | some (_, m) =>
    match fields m with
    | none => true
    | some fs => fs.any fun f => (f.num == 5 || f.num == 14) && (varintValue m f).all (· != 0)

open Examples in
#guard !ephemeral (nonce.bytes ++ bodyField) && ephemeral (nonce.bytes ++ bodyField ++
  bytesOf [0x28, 60]) && ephemeral (nonce.bytes ++ bytesOf [0x70, 1]) &&
  !ephemeral (nonce.bytes ++ bytesOf [0x28, 0]) && ephemeral ⟨#[1, 2]⟩

/-! ## The request and the responder's state -/

/-- A request, as the host passes it to `SERVE`. -/
structure Query where
  /-- The Signal-authenticated sender of the request. -/
  aci : Aci
  /-- The identity key this device holds for `aci` when `SERVE` runs. Server-influenceable
  (TOFU); the host seals the reply to exactly this key, so only its holder can read the content. -/
  key : ByteArray
  /-- The requester's `since`: digests whose past it already has. -/
  since : Array Digest := #[]
  /-- The responder's own `since` for that account (its heads when it saw the account removed,
  JOIN_PLAN §6.5). It is joined with `since`; joining only shrinks what is shown. -/
  ownSince : Array Digest := #[]
  /-- `none`: a catch-up (the whole view). `some ds`: a per-digest repair of `ds`. -/
  wanted : Option (Array Digest) := none
  /-- An export file: refuse disappearing and view-once content (A9). -/
  forExport : Bool := false
  /-- Strict mode (per group, off by default): content only in author copies. -/
  strict : Bool := false

/-- What the responder holds outside the store for one record. -/
structure Held where
  /-- The opening, if this device still holds the content. -/
  opening : Option ByteArray := none
  /-- The audience `zrdtd` recorded from an opening it checked earlier (kept after the content
  is erased). -/
  audience : Option (Array Seat) := none

/-- What the responder holds outside the store, by digest. -/
abbrev HeldMap := Std.ExtTreeMap Digest Held compare

/-- The responder's own state (host state, as A8's facts for `CLASSIFY`). -/
structure Me where
  /-- The responder's ACI. -/
  aci : Aci
  /-- The digests whose provenance on this device is `live`. -/
  live : DigestSet := ∅
  /-- This device's disown set. -/
  disown : DigestSet := ∅
  /-- This store's own boundary digests (empty for a closed store). -/
  boundary : DigestSet := ∅

/-- The responder wrote `r`, holds it `live` (it sent it, or a sync transcript of its own
account did), and has not disowned it. A copy marked so arrives as the author's own; anything
else a responder sends is `relayed(by responder)`, even when the responder is `r.author`. -/
def authorCopy (me : Me) (d : Digest) (r : Rec) : Bool :=
  r.author == me.aci && me.live.contains d && !me.disown.contains d

/-- The opening `o` may go to `q` with the record `r` at `d`: it opens `r`, its own committed
audience seats `q`, an export carries nothing ephemeral, and strict mode sends only author
copies. -/
def serveOpening (me : Me) (q : Query) (d : Digest) (r : Rec) (o : ByteArray) : Bool :=
  openingMatches r.group r.author r.commit o && (audienceOf o).any (seats · q.aci q.key) &&
    !(q.forExport && ephemeral o) && (!q.strict || authorCopy me d r)

/-- The audience the responder knows for `r`: from a matching held opening, else the audience
`zrdtd` recorded. It decides structure only; content is decided by `serveOpening`. -/
def audienceFor (r : Rec) (h : Held) : Option (Array Seat) :=
  match h.opening with
  | some o => if openingMatches r.group r.author r.commit o then audienceOf o else h.audience
  | none => h.audience

/-- `q` is seated in the audience the responder knows for the stored record `r` at `d`. -/
def entitledHere (held : HeldMap) (q : Query) (d : Digest) (r : Rec) : Bool :=
  (audienceFor r (held.getD d {})).any (seats · q.aci q.key)

/-- **What `serveOpening` guarantees.** The opening opens `r`; its own committed audience seats
`q`; an export carries nothing ephemeral; in strict mode, the record is the responder's own. -/
theorem serveOpening_spec {me : Me} {q : Query} {d : Digest} {r : Rec} {o : ByteArray}
    (h : serveOpening me q d r o = true) :
    openingMatches r.group r.author r.commit o = true ∧
      (∃ aud, audienceOf o = some aud ∧ seats aud q.aci q.key = true) ∧
      (q.forExport = true → ephemeral o = false) ∧
      (q.strict = true → authorCopy me d r = true) := by
  simp only [serveOpening, Bool.and_eq_true, Option.any_eq_true, Bool.not_eq_true',
    Bool.and_eq_false_iff, Bool.or_eq_true] at h
  obtain ⟨⟨⟨hm, aud, ha, hs⟩, hx⟩, hst⟩ := h
  refine ⟨hm, ⟨aud, ha, hs⟩, fun hexp => ?_, fun hs' => ?_⟩
  · rcases hx with hx | hx
    · simp [hexp] at hx
    · exact hx
  · rcases hst with hst | hst
    · simp [hs'] at hst
    · exact hst

/-! ## The walks -/

/-- For every stored record, the stored records that link it. -/
def linkedByMap (c : CheckedStore) : Std.ExtTreeMap Digest (List Digest) compare :=
  c.raw.map.foldl (init := c.raw.map.map fun _ _ => []) fun acc d r =>
    r.links.foldl (init := acc) fun acc l => acc.modify l (d :: ·)

/-- The stored records reachable from `q`'s `since` joined with the responder's own `since`. -/
def sinceReach (c : CheckedStore) (q : Query) : DigestSet :=
  c.reachSet (q.since ++ q.ownSince)

/-- The stored records `q` is seated in (as far as the responder knows) and that are not
reachable from `since`. -/
def visList (c : CheckedStore) (held : HeldMap) (q : Query) : List Digest :=
  let sr := sinceReach c q
  c.raw.map.toList.filterMap fun (d, r) =>
    if entitledHere held q d r && !sr.contains d then some d else none

/-- The stored records that reach a `vis` record: the walk backwards from them. -/
def upSet (c : CheckedStore) (held : HeldMap) (q : Query) : DigestSet :=
  walk id (linkedByMap c) ∅ (visList c held q)

/-- The digests linked by the stored records among `ds`. -/
def linksOf (c : CheckedStore) (ds : List Digest) : DigestSet :=
  ds.foldl (init := ∅) fun acc d =>
    match c.get d with
    | some r => r.links.foldl (fun s l => s.insert l) acc
    | none => acc

/-! ## The reply -/

/-- One item of a reply. -/
inductive Entry
  /-- A record sent to the requester: the record, its opening if it may go, and whether this is
  the author's own copy. -/
  | addressed (r : Rec) (opening : Option ByteArray) (authorCopy : Bool)
  /-- A record that reaches one sent to the requester: structure only. -/
  | after (r : Rec)
  /-- A digest only. -/
  | boundary (d : Digest)

/-- The reply to `q` (the table in the module header). In per-digest mode there is an entry for
each wanted digest only, and content for a wanted record `q` is seated in whatever `since` says.
Entries from stored records come first, sorted by digest, then the responder's own boundary
digests, sorted. -/
def serve (c : CheckedStore) (me : Me) (held : HeldMap) (q : Query) : List Entry :=
  let up := upSet c held q
  let sr := sinceReach c q
  let linkedByUp := linksOf c up.toList
  let linkedAny := linksOf c (c.raw.map.toList.map (·.1))
  let perDigest := q.wanted.isSome
  let want : Digest → Bool := fun d => (q.wanted.map (·.contains d)).getD true
  let fromRecords := c.raw.map.toList.filterMap fun (d, r) =>
    if !want d then none
    else if entitledHere held q d r && (perDigest || !sr.contains d) then
      some (.addressed r ((held.getD d {}).opening.filter (serveOpening me q d r))
        (authorCopy me d r))
    else if up.contains d then some (.after r)
    else if perDigest || linkedByUp.contains d || !linkedAny.contains d then some (.boundary d)
    else none
  let fromBoundary := me.boundary.toList.filterMap fun d =>
    if want d && !c.raw.map.contains d &&
        (perDigest || linkedByUp.contains d || !linkedAny.contains d) then
      some (.boundary d)
    else none
  fromRecords ++ fromBoundary

/-! ## What the reply may contain -/

/-- A pair of a stored map's list is a stored record. -/
theorem get_of_mem_toList {c : CheckedStore} {d : Digest} {r : Rec}
    (h : (d, r) ∈ c.raw.map.toList) : c.get d = some r :=
  Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some.1 h

/-- Every addressed entry: a stored record; the author-copy bit is `authorCopy`; an opening only
if `serveOpening` accepts it. -/
theorem serve_addressed {c : CheckedStore} {me : Me} {held : HeldMap} {q : Query} {r : Rec}
    {o : Option ByteArray} {ac : Bool} (he : Entry.addressed r o ac ∈ serve c me held q) :
    ∃ d : Digest, c.get d = some r ∧ ac = authorCopy me d r ∧
      ∀ op, o = some op → serveOpening me q d r op = true := by
  simp only [serve, List.mem_append, List.mem_filterMap] at he
  rcases he with ⟨⟨d, r'⟩, hmem, hf⟩ | ⟨d, -, hf⟩
  · have hget := get_of_mem_toList hmem
    split at hf
    · simp at hf
    · split at hf
      · simp only [Option.some.injEq, Entry.addressed.injEq] at hf
        obtain ⟨rfl, rfl, rfl⟩ := hf
        refine ⟨d, hget, rfl, ?_⟩
        intro op hop
        cases hh : (held.getD d {}).opening with
        | none => simp [hh] at hop
        | some o' =>
          rw [hh] at hop
          simp only [Option.filter] at hop
          split at hop
          · cases hop; assumption
          · simp at hop
      · split at hf
        · simp at hf
        · split at hf <;> simp at hf
  · split at hf <;> simp at hf

/-- **Content goes only where its author sent it.** Every opening in a reply to `q` opens a
stored record (so its audience is the one the author committed to), and that audience seats
`q.aci` with the tag of `q.key`. No author shortcut, no audience cache, no `since`, no host flag
or provenance. -/
theorem serve_content {c : CheckedStore} {me : Me} {held : HeldMap} {q : Query} {r : Rec}
    {o : Option ByteArray} {ac : Bool} (he : Entry.addressed r o ac ∈ serve c me held q) :
    ∃ d : Digest, c.get d = some r ∧
      ∀ op, o = some op → openingMatches r.group r.author r.commit op = true ∧
        ∃ aud, audienceOf op = some aud ∧ seats aud q.aci q.key = true := by
  obtain ⟨d, hget, -, hop⟩ := serve_addressed he
  exact ⟨d, hget, fun op h => ⟨(serveOpening_spec (hop op h)).1, (serveOpening_spec (hop op h)).2.1⟩⟩

/-- **An author copy is the author's own.** An entry marked author copy is a stored record the
responder wrote, holds `live`, and has not disowned. -/
theorem serve_authorCopy {c : CheckedStore} {me : Me} {held : HeldMap} {q : Query} {r : Rec}
    {o : Option ByteArray} (he : Entry.addressed r o true ∈ serve c me held q) :
    ∃ d : Digest, c.get d = some r ∧ r.author = me.aci ∧ me.live.contains d = true ∧
      me.disown.contains d = false := by
  obtain ⟨d, hget, hac, -⟩ := serve_addressed he
  have h := hac.symm
  simp only [authorCopy, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at h
  exact ⟨d, hget, h.1.1, h.1.2, h.2⟩

/-- **Strict mode: content only in author copies.** -/
theorem serve_strict {c : CheckedStore} {me : Me} {held : HeldMap} {q : Query} {r : Rec}
    {op : ByteArray} {ac : Bool} (hs : q.strict = true)
    (he : Entry.addressed r (some op) ac ∈ serve c me held q) : ac = true := by
  obtain ⟨d, -, hac, hop⟩ := serve_addressed he
  rw [hac]
  exact (serveOpening_spec (hop op rfl)).2.2.2 hs

/-- **Exports carry no disappearing or view-once content.** -/
theorem serve_export {c : CheckedStore} {me : Me} {held : HeldMap} {q : Query} {r : Rec}
    {op : ByteArray} {ac : Bool} (hx : q.forExport = true)
    (he : Entry.addressed r (some op) ac ∈ serve c me held q) : ephemeral op = false := by
  obtain ⟨d, -, -, hop⟩ := serve_addressed he
  exact (serveOpening_spec (hop op rfl)).2.2.1 hx

/-- **The converse of `serve_content`.** Every held opening that `serveOpening` accepts for its
stored record is in the reply, marked author copy exactly when it is one: in a catch-up when
`since` does not reach it, in a per-digest repair when it is wanted. With `serve_content`, the content of a reply is exactly that set. It
depends on the store, the held openings, the responder's own state (strict mode only) and `q`,
and on nothing else: not the audience cache, not the structure entries. `q.key` is
server-influenceable (TOFU); the host seals the reply to it (JOIN_PLAN §4.3). -/
theorem serve_content_complete {c : CheckedStore} {me : Me} {held : HeldMap} {q : Query}
    {d : Digest} {r : Rec} {op : ByteArray}
    (hget : c.get d = some r) (hop : (held.getD d {}).opening = some op)
    (hs : serveOpening me q d r op = true)
    (hw : (q.wanted.map (·.contains d)).getD true = true)
    (hsr : q.wanted.isSome = true ∨ (sinceReach c q).contains d = false) :
    Entry.addressed r (some op) (authorCopy me d r) ∈ serve c me held q := by
  have hm : openingMatches r.group r.author r.commit op = true := (serveOpening_spec hs).1
  have hent : entitledHere held q d r = true := by
    simp only [serveOpening, Bool.and_eq_true] at hs
    simp only [entitledHere, audienceFor, hop, hm, ite_true]
    exact hs.1.1.2
  simp only [serve, List.mem_append, List.mem_filterMap]
  refine .inl ⟨(d, r), Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some.2 hget, ?_⟩
  have hcond : (entitledHere held q d r && (q.wanted.isSome || !(sinceReach c q).contains d)) =
      true := by
    rcases hsr with h | h <;> simp [hent, h]
  simp only [hw, Bool.not_true, Bool.false_eq_true, ite_false, hcond, ite_true, hop,
    Option.filter, hs]

/-- **Structure without content** goes only for stored records in the walk back from the records
`q` is seated in and that `since` does not reach. -/
theorem serve_after {c : CheckedStore} {me : Me} {held : HeldMap} {q : Query} {r : Rec}
    (he : Entry.after r ∈ serve c me held q) :
    ∃ d : Digest, c.get d = some r ∧ d ∈ upSet c held q := by
  simp only [serve, List.mem_append, List.mem_filterMap] at he
  rcases he with ⟨⟨d, r'⟩, hmem, hf⟩ | ⟨d, -, hf⟩
  · have hget := get_of_mem_toList hmem
    split at hf
    · simp at hf
    · split at hf
      · simp at hf
      · split at hf
        · rename_i hup
          simp only [Option.some.injEq, Entry.after.injEq] at hf
          subst hf
          exact ⟨d, hget, Std.ExtTreeSet.contains_iff_mem.1 hup⟩
        · split at hf <;> simp at hf
  · split at hf <;> simp at hf

/-- **A boundary digest hides nothing sent to `q`.** It is a stored record outside the walk (so
it reaches no record `q` is seated in beyond `since`), and if `q` is seated in it, this is a
catch-up and `since` already reaches it; or it is a digest of the responder's own boundary that
the store does not hold. -/
theorem serve_boundary {c : CheckedStore} {me : Me} {held : HeldMap} {q : Query} {d : Digest}
    (he : Entry.boundary d ∈ serve c me held q) :
    (∃ r, c.get d = some r ∧ d ∉ upSet c held q ∧
      (entitledHere held q d r = true → q.wanted = none ∧ (sinceReach c q).contains d = true)) ∨
    (me.boundary.contains d = true ∧ c.has d = false) := by
  simp only [serve, List.mem_append, List.mem_filterMap] at he
  rcases he with ⟨⟨d', r⟩, hmem, hf⟩ | ⟨d', hmem, hf⟩
  · have hget := get_of_mem_toList hmem
    split at hf
    · simp at hf
    · split at hf
      · simp at hf
      · rename_i hent
        split at hf
        · simp at hf
        · rename_i hup
          split at hf
          · simp only [Option.some.injEq, Entry.boundary.injEq] at hf
            subst hf
            refine .inl ⟨r, hget, fun hm => hup (Std.ExtTreeSet.contains_iff_mem.2 hm), ?_⟩
            intro he'
            simp only [he', Bool.true_and, Bool.or_eq_true, Bool.not_eq_true', not_or,
              Bool.not_eq_false] at hent
            refine ⟨?_, hent.2⟩
            cases hw : q.wanted with
            | none => rfl
            | some ws => simp [hw] at hent
          · simp at hf
  · split at hf
    · rename_i hc
      simp only [Option.some.injEq, Entry.boundary.injEq] at hf
      subst hf
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hc
      exact .inr ⟨Std.ExtTreeSet.contains_iff_mem.2 (Std.ExtTreeSet.mem_toList.1 hmem), hc.1.2⟩
    · simp at hf

/-! ## The audience is bound by the commitment -/

/-- **One commit, one audience.** Two openings that both match one commit (by one author in one
group) have the same audience, or SHA-256 has a collision. So a relay cannot rewrite the audience
of a real message: the rewritten opening fails `openingMatches`. -/
theorem audience_bound {g : GroupId} {a : Aci} {c : Digest} {o₁ o₂ : ByteArray}
    (h₁ : openingMatches g a c o₁ = true) (h₂ : openingMatches g a c o₂ = true) :
    audienceOf o₁ = audienceOf o₂ ∨ ∃ x y : ByteArray, x ≠ y ∧ sha256 x = sha256 y := by
  obtain ⟨n₁, m₁, rfl, hb₁, hc₁⟩ := openingMatches_spec h₁
  obtain ⟨n₂, m₂, rfl, hb₂, hc₂⟩ := openingMatches_spec h₂
  simp only [commit, hb₁, hb₂, Option.map_some, Option.some.injEq] at hc₁ hc₂
  let P := commitTag ++ g.bytes ++ a.bytes
  have e₁ : commitTag ++ g.bytes ++ a.bytes ++ n₁.bytes ++ m₁ = P ++ (n₁.bytes ++ m₁) :=
    ByteArray.append_assoc
  have e₂ : commitTag ++ g.bytes ++ a.bytes ++ n₂.bytes ++ m₂ = P ++ (n₂.bytes ++ m₂) :=
    ByteArray.append_assoc
  rw [e₁] at hc₁
  rw [e₂] at hc₂
  by_cases hx : P ++ (n₁.bytes ++ m₁) = P ++ (n₂.bytes ++ m₂)
  · exact .inl (congrArg audienceOf ((ByteArray.append_right_inj P).1 hx))
  · exact .inr ⟨_, _, hx, hc₁.trans hc₂.symm⟩

/-! ## Examples (the tests of JOIN_PLAN §7.1)

Carol writes `pre` before Bob joins (audience Alice and Carol). Alice writes `welcome` after the
add (Bob seated), linking `pre`. Carol, whose view of the members lags the add, writes `stale`
(Bob not seated), linking `welcome`. Alice writes `later` (Bob seated), linking `stale`. Alice is
the responder; she holds every opening. -/

namespace Examples
open Zrdt.Examples

/-- More members (byte order: alice, bob, carol, dave, eve, mallory). -/
def dave : Aci := ⟨⟨Array.replicate 16 0xd4⟩, rfl⟩
/-- A later newcomer. -/
def eve : Aci := ⟨⟨Array.replicate 16 0xe5⟩, rfl⟩
/-- A member Alice blocked. -/
def mallory : Aci := ⟨⟨Array.replicate 16 0xee⟩, rfl⟩

/-- An identity key, 33 bytes serialized. -/
def idKey (n : UInt8) : ByteArray := ⟨Array.replicate 33 n⟩
/-- Alice's identity key. -/
def keyAlice : ByteArray := idKey 1
/-- Bob's identity key. -/
def keyBob : ByteArray := idKey 2
/-- Carol's identity key. -/
def keyCarol : ByteArray := idKey 3
/-- Eve's identity key. -/
def keyEve : ByteArray := idKey 5
/-- Mallory's identity key. -/
def keyMallory : ByteArray := idKey 6
/-- A key the server swapped in for Bob. -/
def keyBob' : ByteArray := idKey 0x99
/-- A key the server swapped in for Carol. -/
def keyCarol' : ByteArray := idKey 0x98

/-- A nonce of 32 bytes `n`. -/
def nonceOf (n : UInt8) : Nonce := ⟨⟨Array.replicate 32 n⟩, rfl⟩

/-- A varint below 2^14. -/
def varint2 (n : Nat) : ByteArray :=
  if n < 128 then bytesOf [n] else bytesOf [n % 128 + 128, n / 128]

/-- The audience of `es`: each member with the tag of its key, or the zero tag (`none`). -/
def audienceOfKeys (es : List (Aci × Option ByteArray)) : Array Seat :=
  es.toArray.map fun (a, k) => ⟨a, (k.map keyTag).getD zeroTag⟩

/-- Field 201 (key 1610 = 201 · 8 + 2, the varint `ca 0c`) holding the audience of `es`. -/
def audienceFieldOf (es : List (Aci × Option ByteArray)) : ByteArray :=
  let payload := writeAudience (audienceOfKeys es)
  bytesOf [0xca, 0x0c] ++ varint2 payload.size ++ payload

/-- Field 1 (`body`) holding `s` (under 128 bytes). -/
def textField (s : String) : ByteArray := bytesOf [0x0a, s.utf8ByteSize] ++ s.toUTF8

/-- A group message: the body, the group context (field 15) and the audience (field 201). -/
def message (s : String) (es : List (Aci × Option ByteArray)) : ByteArray :=
  textField s ++ groupV2Field ++ audienceFieldOf es

/-- A disappearing message: field 5 (`expireTimer`) = 60. -/
def messageTimer (s : String) (es : List (Aci × Option ByteArray)) : ByteArray :=
  message s es ++ bytesOf [0x28, 60]

/-- The record and the opening of message `m` by `a`, with nonce byte `n` and links `ls`. -/
def mkMsg (a : Aci) (n : UInt8) (m : ByteArray) (ls : Array Digest) : Rec × ByteArray :=
  match commitWithOpening group a (nonceOf n) m with
  | some (c, o) => (Rec.make group c ls a, o)
  | none => (Rec.make group Digest.zero ls a, ByteArray.empty)

/-- The record and the opening of text `s` by `a` with audience `es`. -/
def mk (a : Aci) (n : UInt8) (s : String) (es : List (Aci × Option ByteArray))
    (ls : Array Digest) : Rec × ByteArray :=
  mkMsg a n (message s es) ls

/-- Alice and Carol, under their keys. -/
def AC : List (Aci × Option ByteArray) := [(alice, some keyAlice), (carol, some keyCarol)]
/-- Alice, Bob and Carol, under their keys. -/
def ABC : List (Aci × Option ByteArray) :=
  [(alice, some keyAlice), (bob, some keyBob), (carol, some keyCarol)]

/-- Carol, before Bob joined. -/
def pre : Rec × ByteArray := mk carol 1 "pre-join secret" AC #[]
/-- Alice, after the add: Bob seated. -/
def welcome : Rec × ByteArray := mk alice 2 "welcome bob" ABC #[hashRecord pre.1]
/-- Carol with a stale view: Bob not seated. -/
def stale : Rec × ByteArray := mk carol 3 "stale view" AC #[hashRecord welcome.1]
/-- Alice again: Bob seated. -/
def later : Rec × ByteArray := mk alice 4 "later" ABC #[hashRecord stale.1]

/-- The store with the four records. -/
def store : CheckedStore :=
  ((CheckedStore.empty group).acceptAll #[pre.1, welcome.1, stale.1, later.1]).1

/-- Openings, by digest. -/
def heldOf (l : List (Rec × ByteArray)) : HeldMap :=
  Std.ExtTreeMap.ofList (l.map fun (r, o) => (hashRecord r, ({ opening := some o } : Held)))
    compare

/-- Alice holds every opening. -/
def held : HeldMap := heldOf [pre, welcome, stale, later]

/-- A request from `a` under key `k`. -/
def rq (a : Aci) (k : ByteArray) (since : Array Digest := #[])
    (wanted : Option (Array Digest) := none) (forExport := false) (strict := false) : Query :=
  { aci := a, key := k, since, wanted, forExport, strict }

/-- Alice, closed store, her own records `live`. -/
def meAlice : Me :=
  { aci := alice, live := Std.ExtTreeSet.ofList [hashRecord welcome.1, hashRecord later.1] }

/-- The records whose content a reply carries. -/
def contentOf (es : List Entry) : List Rec :=
  es.filterMap fun | .addressed r (some _) _ => some r | _ => none

/-- The records a reply carries as `after` structures. -/
def afterOf (es : List Entry) : List Rec :=
  es.filterMap fun | .after r => some r | _ => none

/-- The digests a reply carries as boundary entries. -/
def boundaryOf (es : List Entry) : List Digest :=
  es.filterMap fun | .boundary d => some d | _ => none

-- The opening keeps field 201 and drops field 15.
#guard (audienceOf pre.2).map (·.map (·.aci)) == some #[alice, carol]
#guard openingMatches group carol pre.1.commit pre.2
#guard store.size == 4

-- Bob never gets `pre`'s content: `pre` goes to him as a boundary digest only.
#guard contentOf (serve store meAlice held (rq bob keyBob)) == [welcome.1, later.1] ||
  contentOf (serve store meAlice held (rq bob keyBob)) == [later.1, welcome.1]
#guard boundaryOf (serve store meAlice held (rq bob keyBob)) == [hashRecord pre.1]
-- Carol's stale-view record goes to Bob as structure (`after`), never content.
#guard afterOf (serve store meAlice held (rq bob keyBob)) == [stale.1]
-- Carol, seated with her own key, gets `pre`'s content.
#guard (contentOf (serve store meAlice held (rq carol keyCarol))).contains pre.1
-- No author shortcut: Carol under a swapped key gets nothing, not even her own records.
#guard contentOf (serve store meAlice held (rq carol keyCarol')) == []
-- A requester whose identity key changed gets no content.
#guard contentOf (serve store meAlice held (rq bob keyBob')) == []
-- Alice's own records go out as author copies; Carol's do not.
#guard (serve store meAlice held (rq bob keyBob)).all fun
  | .addressed r _ ac => ac == (r.author == alice) | _ => true

/-- A relay rewrites `pre`'s audience to seat Bob, keeping the nonce. -/
def forgedOpening : ByteArray :=
  match commitWithOpening group carol (nonceOf 1) (message "pre-join secret" ABC) with
  | some (_, o) => o
  | none => ByteArray.empty

-- The rewritten opening does not match `pre`'s commit, so it is never served.
#guard !openingMatches group carol pre.1.commit forgedOpening
#guard !serveOpening meAlice (rq bob keyBob) (hashRecord pre.1) pre.1 forgedOpening
#guard !(contentOf (serve store meAlice (held.insert (hashRecord pre.1)
  { opening := some forgedOpening }) (rq bob keyBob))).contains pre.1

/-- An opening of a message without field 201 (refused when stored; never served). -/
def noAudience : Rec × ByteArray := mkMsg alice 14 (textField "no audience" ++ groupV2Field) #[]
#guard audienceOf noAudience.2 == none
#guard contentOf (serve ((CheckedStore.empty group).acceptAll #[noAudience.1]).1
  { aci := alice, live := Std.ExtTreeSet.ofList [hashRecord noAudience.1] } (heldOf [noAudience])
  (rq alice keyAlice)) == []

/-- Mallory is blocked: in the audience with the zero tag. -/
def toBob : Rec × ByteArray :=
  mk alice 7 "not for mallory" [(alice, some keyAlice), (bob, some keyBob), (mallory, none)] #[]
/-- The store with `toBob`. -/
def storeM : CheckedStore := ((CheckedStore.empty group).acceptAll #[toBob.1]).1
#guard contentOf (serve storeM meAlice (heldOf [toBob]) (rq mallory keyMallory)) == []
#guard contentOf (serve storeM meAlice (heldOf [toBob]) (rq bob keyBob)) == [toBob.1]

/-- A forgery "by Alice", relayed to Alice by Mallory (A8: she accepts and disowns it); its
audience seats Bob. -/
def forgery : Rec × ByteArray := mk alice 8 "forged in alice's name" ABC #[]
/-- The store with the forgery. -/
def storeF : CheckedStore := ((CheckedStore.empty group).acceptAll #[forgery.1]).1
/-- Alice, who disowned the forgery. -/
def meAliceF : Me := { aci := alice, disown := Std.ExtTreeSet.ofList [hashRecord forgery.1] }
-- Alice serves its content to Bob (its own audience seats him), never as an author copy.
#guard contentOf (serve storeF meAliceF (heldOf [forgery]) (rq bob keyBob)) == [forgery.1]
#guard (serve storeF meAliceF (heldOf [forgery]) (rq bob keyBob)).all fun
  | .addressed _ _ ac => !ac | _ => true
-- Strict mode: the forgery's content does not go out at all.
#guard contentOf (serve storeF meAliceF (heldOf [forgery]) (rq bob keyBob (strict := true))) == []

/-- A message Carol sent to all three. -/
def fromCarol : Rec × ByteArray := mk carol 15 "carol to all" ABC #[]
/-- Alice's own message to all three, after it. -/
def fromAlice : Rec × ByteArray := mk alice 16 "alice to all" ABC #[hashRecord fromCarol.1]
/-- The store with both. -/
def storeS : CheckedStore := ((CheckedStore.empty group).acceptAll #[fromCarol.1, fromAlice.1]).1
/-- Alice holds her own `live`. -/
def meAliceS : Me := { aci := alice, live := Std.ExtTreeSet.ofList [hashRecord fromAlice.1] }
-- Off by default: Alice relays Carol's message and sends her own.
#guard (contentOf (serve storeS meAliceS (heldOf [fromCarol, fromAlice]) (rq bob keyBob))).length
  == 2
-- Strict mode: only Alice's own author copy carries content; Carol's goes as structure.
#guard contentOf (serve storeS meAliceS (heldOf [fromCarol, fromAlice])
  (rq bob keyBob (strict := true))) == [fromAlice.1]
#guard (serve storeS meAliceS (heldOf [fromCarol, fromAlice]) (rq bob keyBob (strict := true))).any
  fun | .addressed r none false => r == fromCarol.1 | _ => false

/-- A disappearing message. -/
def timed : Rec × ByteArray := mkMsg alice 9 (messageTimer "disappears" ABC) #[]
/-- The store with it. -/
def storeT : CheckedStore := ((CheckedStore.empty group).acceptAll #[timed.1]).1
-- An export refuses it; a relay carries it.
#guard ephemeral timed.2 && !ephemeral welcome.2
#guard contentOf (serve storeT meAlice (heldOf [timed]) (rq bob keyBob (forExport := true))) == []
#guard contentOf (serve storeT meAlice (heldOf [timed]) (rq bob keyBob)) == [timed.1]

/-- Re-add: `ra1` (Bob seated), Bob removed, `gap` (Carol, Bob not seated), Bob re-added, `ra2`
(Bob seated). -/
def ra1 : Rec × ByteArray := mk alice 10 "before removal" ABC #[]
/-- Written while Bob was out. -/
def gap : Rec × ByteArray := mk carol 11 "while bob was out" AC #[hashRecord ra1.1]
/-- After the re-add. -/
def ra2 : Rec × ByteArray := mk alice 12 "after re-add" ABC #[hashRecord gap.1]
/-- The store with the three. -/
def storeR : CheckedStore := ((CheckedStore.empty group).acceptAll #[ra1.1, gap.1, ra2.1]).1
/-- Alice holds the three openings. -/
def heldR : HeldMap := heldOf [ra1, gap, ra2]
-- With `since` = his old heads, the gap comes back as a digest; without it, as `after`.
#guard afterOf (serve storeR meAlice heldR (rq bob keyBob (since := #[hashRecord ra1.1]))) == []
#guard afterOf (serve storeR meAlice heldR (rq bob keyBob)) == [gap.1]
-- The responder's own `since` for Bob does the same when Bob sends none.
#guard afterOf (serve storeR meAlice heldR
  { rq bob keyBob with ownSince := #[hashRecord ra1.1] }) == []
-- A per-digest repair of `ra1` returns its content even when `since` reaches it.
#guard contentOf (serve storeR meAlice heldR
  (rq bob keyBob (since := #[hashRecord ra1.1]) (wanted := some #[hashRecord ra1.1]))) == [ra1.1]
-- A per-digest request for the gap record gives its digest only.
#guard (serve storeR meAlice heldR
    (rq bob keyBob (since := #[hashRecord ra1.1]) (wanted := some #[hashRecord gap.1]))).all fun
  | .boundary _ => true | _ => false

/-- Crawl attempts by the newcomer: every `since` and `wanted` shape. -/
def crawls : List Query :=
  [rq bob keyBob, rq bob keyBob (wanted := some #[hashRecord pre.1]),
   rq bob keyBob (since := #[hashRecord later.1]), rq bob keyBob (since := #[hashRecord pre.1]),
   rq bob keyBob (wanted := some #[hashRecord pre.1, hashRecord welcome.1, hashRecord stale.1])]
-- None returns `pre`'s content or structure.
#guard crawls.all fun cq => (serve store meAlice held cq).all fun
  | .addressed r _ _ => r != pre.1
  | .after r => r != pre.1
  | .boundary _ => true

/-- The H3 regression: v1 served an opening when the record's revision was at least the
requester's join revision as the server reported it. -/
def v1Serves (rev joinRev : Nat) : Bool := rev ≥ joinRev
-- `stale` was written at revision 8; the server says Bob joined at 5 (he joined at 9). v1
-- releases `stale`; `serve` does not.
#guard v1Serves 8 5
#guard !(contentOf (serve store meAlice held (rq bob keyBob))).contains stale.1

-- The responder's own boundary: a digest it holds no record for is served as a digest, at the
-- head (nothing stored links it), and for a per-digest request that wants it.
#guard boundaryOf (serve storeS { meAliceS with boundary := Std.ExtTreeSet.ofList [dig 0x77] }
  (heldOf [fromCarol, fromAlice]) (rq bob keyBob)) == [dig 0x77]
#guard boundaryOf (serve storeS { meAliceS with boundary := Std.ExtTreeSet.ofList [dig 0x77] }
  (heldOf [fromCarol, fromAlice]) (rq bob keyBob (wanted := some #[dig 0x77]))) == [dig 0x77]

/-! ## The theorems on real inputs

Each main theorem is instantiated on a real message with every hypothesis discharged (the kernel
runs SHA-256 here, so the inputs are one small message), and the content statement rejects the
leak it is meant to stop. -/

/-- Alice's message to herself: the smallest audience. -/
def selfMsg : Rec × ByteArray := mk alice 20 "hi" [(alice, some keyAlice)] #[]
/-- The store holding only it. -/
def selfStore : CheckedStore := ((CheckedStore.empty group).accept selfMsg.1).2
/-- Its digest. -/
def selfDigest : Digest := hashRecord selfMsg.1
/-- Alice holds it `live`. -/
def selfMe : Me := { aci := alice, live := (∅ : DigestSet).insert selfDigest }
/-- Alice holds its opening. -/
def selfHeld : HeldMap := (∅ : HeldMap).insert selfDigest { opening := some selfMsg.2 }

/-- The opening matches the record (the kernel computes the commitment). -/
theorem selfMsg_matches :
    openingMatches selfMsg.1.group selfMsg.1.author selfMsg.1.commit selfMsg.2 = true := by
  decide +kernel

/-- Its committed audience seats Alice under her key (the kernel computes the key tag). -/
theorem selfMsg_seats : ∃ aud, audienceOf selfMsg.2 = some aud ∧ seats aud alice keyAlice = true := by
  have h : (audienceOf selfMsg.2).any (seats · alice keyAlice) = true := by decide +kernel
  simpa only [Option.any_eq_true] using h

/-- It is not ephemeral. -/
theorem selfMsg_lasting : ephemeral selfMsg.2 = false := by decide +kernel

/-- The store holds it under its digest. -/
theorem selfStore_get : selfStore.get selfDigest = some selfMsg.1 := by
  have hl : selfMsg.1.links = #[] := by decide +kernel
  have hok : (rawAccept (CheckedStore.empty group).raw selfMsg.1).1 = .accepted selfDigest :=
    rawAccept_of_ok (by decide +kernel) (by simp [Rec.WellSized, hl, maxLinks])
      (by simp [hl]) (by simp [CheckedStore.empty]) (by simp [CheckedStore.empty, maxRecords])
  have h := rawAccept_accepted (c' := (rawAccept (CheckedStore.empty group).raw selfMsg.1).2)
    (Prod.ext hok rfl)
  show (rawAccept (CheckedStore.empty group).raw selfMsg.1).2.map[selfDigest]? = some selfMsg.1
  rw [h.2.2.1]
  exact Std.ExtTreeMap.getElem?_insert_self

/-- `serveOpening` accepts it for Alice, in a catch-up, an export, and strict mode. -/
theorem selfMsg_serveOpening (forExport strict : Bool) :
    serveOpening selfMe (rq alice keyAlice (forExport := forExport) (strict := strict)) selfDigest
      selfMsg.1 selfMsg.2 = true := by
  obtain ⟨aud, ha, hs⟩ := selfMsg_seats
  have hac : authorCopy selfMe selfDigest selfMsg.1 = true := by
    have hauth : selfMsg.1.author = alice := by decide +kernel
    simp [authorCopy, selfMe, hauth]
  simp [serveOpening, rq, selfMsg_matches, ha, hs, selfMsg_lasting, hac]

/-- **Satisfiable:** the reply to Alice's catch-up holds her message with its opening, as an
author copy (via `serve_content_complete`). -/
theorem self_served (forExport strict : Bool) :
    Entry.addressed selfMsg.1 (some selfMsg.2) true ∈
      serve selfStore selfMe selfHeld (rq alice keyAlice (forExport := forExport) (strict := strict)) := by
  have hac : authorCopy selfMe selfDigest selfMsg.1 = true := by
    have hauth : selfMsg.1.author = alice := by decide +kernel
    simp [authorCopy, selfMe, hauth]
  have := serve_content_complete (me := selfMe) (held := selfHeld)
    (q := rq alice keyAlice (forExport := forExport) (strict := strict)) selfStore_get
    (by simp [selfHeld]) (selfMsg_serveOpening forExport strict) (by simp [rq])
    (Or.inr (by simp [sinceReach, rq, CheckedStore.reachSet, walk]))
  rwa [hac] at this

/-- `serve_content`, `serve_authorCopy`, `serve_export` and `serve_strict` applied to it. -/
example : ∃ d, selfStore.get d = some selfMsg.1 ∧ ∀ op, some selfMsg.2 = some op →
    openingMatches selfMsg.1.group selfMsg.1.author selfMsg.1.commit op = true ∧
      ∃ aud, audienceOf op = some aud ∧
        seats aud (rq alice keyAlice).aci (rq alice keyAlice).key = true :=
  serve_content (self_served false false)
example : ∃ d, selfStore.get d = some selfMsg.1 ∧ selfMsg.1.author = selfMe.aci ∧
    selfMe.live.contains d = true ∧ selfMe.disown.contains d = false :=
  serve_authorCopy (self_served false false)
example : ephemeral selfMsg.2 = false := serve_export rfl (self_served true false)
example : true = true := serve_strict rfl (self_served false true)

/-- `audience_bound` applied to the opening and itself. -/
example : audienceOf selfMsg.2 = audienceOf selfMsg.2 ∨
    ∃ x y : ByteArray, x ≠ y ∧ sha256 x = sha256 y :=
  audience_bound selfMsg_matches selfMsg_matches

/-- What `serve_content` promises of a reply to `q`: every opening in it is committed with an
audience that seats `q`. -/
def ContentOk (q : Query) (es : List Entry) : Prop :=
  ∀ r op ac, Entry.addressed r (some op) ac ∈ es →
    ∃ aud, audienceOf op = some aud ∧ seats aud q.aci q.key = true

/-- Every reply of `serve` satisfies `ContentOk`. -/
theorem serve_contentOk (c : CheckedStore) (me : Me) (held : HeldMap) (q : Query) :
    ContentOk q (serve c me held q) := fun _ op _ he =>
  let ⟨_, _, h⟩ := serve_content he
  (h op rfl).2

/-- **Rejecting:** a reply that gives Bob the opening of `pre` (Carol's message from before he
joined) breaks `ContentOk`: `pre`'s audience seats only Alice and Carol. -/
example : ¬ ContentOk (rq bob keyBob) [.addressed pre.1 (some pre.2) false] := by
  intro h
  obtain ⟨aud, ha, hs⟩ := h pre.1 pre.2 false (List.mem_singleton.2 rfl)
  have hno : (audienceOf pre.2).any (seats · bob keyBob) = false := by decide +kernel
  simp only [rq] at hs
  simp [ha, hs] at hno

/-- **Rejecting:** the same for Bob under a key the server swapped in, for one of Alice's own
messages that seats him under his real key. -/
example : ¬ ContentOk (rq bob keyBob') [.addressed toBob.1 (some toBob.2) true] := by
  intro h
  obtain ⟨aud, ha, hs⟩ := h toBob.1 toBob.2 true (List.mem_singleton.2 rfl)
  have hno : (audienceOf toBob.2).any (seats · bob keyBob') = false := by decide +kernel
  simp only [rq] at hs
  simp [ha, hs] at hno

end Examples

end Serve
end Zrdt
