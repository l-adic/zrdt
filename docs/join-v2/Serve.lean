-- Reference copy from the JOIN_PLAN v2 review, revised after review round 1 (2026-11-01). Not
-- built by any lake target. Checked with `lake env lean` against core/ at a079b3e, placed under
-- core/Scratch/. No sorry.
import Zrdt.Provenance
import Zrdt.Commit

/-!
# The responder (scratch): what a member sends another member about its store

The audience of a message is a new top-level `DataMessage` field (201): for each member the author
addressed, its ACI and the tag of the identity key the author held for it (16 zero bytes for a
member Signal does not send to: blocked, seen as unregistered, or no key). Field 201 is NOT field
15 or 200, so it stays in the committed bytes: `openingMatches` binds it to the record's commit,
and through the commit to the record's digest. Only holders of the opening (the addressees) see it.

`serve c me held q` answers requester `q` (ACI, the identity key this device holds for it, `since`,
optionally the digests it wants, and an export flag) from a responder whose store `c` may be
relative: its records may link digests in its own boundary `me.boundary` (a former newcomer).
* `addressed r o ac`: `q` is seated in `r`'s audience (non-zero tag of `q.key`); `o` is the opening,
  sent only if it matches `r.commit`, its OWN committed audience seats `q`, and (for an export) the
  message neither disappears nor is view-once; `ac` (author copy) only if the responder wrote `r`,
  holds it as `live`, and has not disowned it;
* `after r`: `r` reaches a record `q` is seated in and that is not reachable from `since`; its
  structure, never content;
* `boundary d`: a stored record outside that walk, or a digest of the responder's own boundary,
  linked by a served record or a head; the digest only;
* nothing: otherwise.
There is no author shortcut: the author is seated through its own audience entry, with its own key.
The one fallback is the responder's own pre-upgrade records, which carry no field 201: for those
only, and only if it wrote them, holds them `live` and has not disowned them, the responder uses
its recorded sent-to list (`Me.sentTo`, from Desktop's `sendStateByConversationId`). No other
member ever serves content without a committed audience.
-/

namespace Zrdt
namespace Serve

/-- The field that carries the audience. -/
def audienceField : Nat := 201

/-- One audience entry: an account and the tag of the identity key the author held for it. -/
structure Seat where
  aci : Aci
  tag : Array UInt8
deriving DecidableEq

/-- The tag of a member Signal does not send to (blocked, unregistered, no key). Seats nobody. -/
def zeroTag : Array UInt8 := Array.replicate 16 0

/-- The tag of an identity key (33 bytes serialized): 16 bytes of SHA-256("zrdtK1" ‖ key). -/
def keyTag (key : ByteArray) : Array UInt8 :=
  ((sha256 ("zrdtK1".toUTF8 ++ key)).bytes.extract 0 16).data

/-- The value bytes of length-delimited field `f` of `m`. -/
def fieldValue (m : ByteArray) (f : Field) : Option ByteArray := do
  let (key, p) ← readVarint m f.start
  guard (key &&& 7 = 2)
  let (len, q) ← readVarint m p
  guard (q + len ≤ m.size)
  pure (m.extract q (q + len))

/-- The value of varint field `f` of `m`. -/
def varintValue (m : ByteArray) (f : Field) : Option Nat := do
  let (key, p) ← readVarint m f.start
  guard (key &&& 7 = 0)
  let (v, _) ← readVarint m p
  pure v

/-- Field-201 bytes: 1 to 256 entries of aci(16) ‖ tag(16), strictly increasing by aci. -/
def parseAudience (b : ByteArray) : Option (Array Seat) := do
  guard (b.size % 32 = 0 ∧ 32 ≤ b.size ∧ b.size ≤ 32 * 256)
  let seats ← (List.range (b.size / 32)).toArray.mapM fun i => do
    let a ← Aci.ofBytes? (b.extract (32 * i) (32 * i + 16))
    pure ({ aci := a, tag := (b.extract (32 * i + 16) (32 * i + 32)).data } : Seat)
  guard ((seats.toList.zip seats.toList.tail).all fun (x, y) => compare x.aci y.aci == .lt)
  pure seats

/-- The audience committed in an opening: exactly one well-formed field 201 in its committed
bytes. -/
def audienceOf (o : ByteArray) : Option (Array Seat) := do
  let (_, m) ← splitOpening o
  let fs ← fields m
  match (fs.filter (·.num == audienceField)).toList with
  | [f] => parseAudience (← fieldValue m f)
  | _ => none

/-- `aud` seats the account `aci` whose identity key (as this device holds it) is `key`: an entry
with that ACI and that key's tag, and the tag is not zero. -/
def seats (aud : Array Seat) (aci : Aci) (key : ByteArray) : Bool :=
  aud.any fun s => s.aci == aci && s.tag == keyTag key && s.tag != zeroTag

/-- The committed message disappears or is view-once: top-level field 5 (`expireTimer`) or 14
(`isViewOnce`) is non-zero. Anything unparseable counts as ephemeral. -/
def ephemeral (o : ByteArray) : Bool :=
  match splitOpening o with
  | none => true
  | some (_, m) =>
    match fields m with
    | none => true
    | some fs => fs.any fun f => (f.num == 5 || f.num == 14) && (varintValue m f).all (· != 0)

/-- A request, as the host passes it to `SERVE`. -/
structure Query where
  /-- The Signal-authenticated sender of the request. -/
  aci : Aci
  /-- The identity key this device holds for `aci` when `SERVE` runs. Server-influenceable (TOFU);
  the host seals the reply to exactly this key, so only its holder can read the content. -/
  key : ByteArray
  /-- The requester's `since`, joined with this responder's own `since` for that account. -/
  since : Array Digest
  /-- `none`: a catch-up (the whole view). `some ds`: a per-digest repair of `ds`. -/
  wanted : Option (Array Digest) := none
  /-- An export file: refuse disappearing and view-once content (A9). -/
  forExport : Bool := false

/-- What the host holds outside the store for one record. -/
structure Held where
  /-- The opening, if this device still holds the content. -/
  opening : Option ByteArray := none
  /-- The audience, cached from an opening checked earlier (kept after the content is erased). -/
  audience : Option (Array Seat) := none

/-- The responder's own state (host state, as A8's `Fact`s for `classify`). -/
structure Me where
  /-- The responder's ACI. -/
  aci : Aci
  /-- The digests whose provenance on this device is `live`. -/
  live : DigestSet := ∅
  /-- This device's disown set. -/
  disown : DigestSet := ∅
  /-- This store's own boundary digests (empty for a closed store). -/
  boundary : DigestSet := ∅
  /-- For the responder's own records that carry no field 201 (written before the upgrade): the
  accounts Signal sent each to (`sendStateByConversationId` keys, copied to `zrdtSentTo` at Phase 1
  start), each with the tag of the identity key held then. -/
  sentTo : Std.ExtTreeMap Digest (Array Seat) compare := ∅

/-- The responder wrote `r`, holds it as `live` (it sent it, or a sync transcript of its own
account), and has not disowned it. A copy marked so is the author's own; anything else a
responder sends is `relayed(by responder)` on the receiver, even when the responder is `r.author`. -/
def authorCopy (me : Me) (d : Digest) (r : Rec) : Bool :=
  r.author == me.aci && me.live.contains d && !me.disown.contains d

/-- The recorded sent-to list, only for the responder's own live, undisowned record. -/
def ownSentTo (me : Me) (d : Digest) (r : Rec) : Option (Array Seat) :=
  if authorCopy me d r then me.sentTo[d]? else none

/-- The audience `SERVE` uses for opening `o` of the record `r` at `d`: its own committed field
201; for an opening without one, the responder's own recorded sent-to list (`ownSentTo`). -/
def openingAudience (me : Me) (d : Digest) (r : Rec) (o : ByteArray) : Option (Array Seat) :=
  (audienceOf o).or (ownSentTo me d r)

/-- The opening `o` may go to `q`: it opens `r`, its audience (`openingAudience`) seats `q`, and an
export carries no disappearing or view-once message. -/
def serveOpening (me : Me) (q : Query) (d : Digest) (r : Rec) (o : ByteArray) : Bool :=
  openingMatches r.group r.author r.commit o && (openingAudience me d r o).any (seats · q.aci q.key) &&
    !(q.forExport && ephemeral o)

/-- The audience the responder knows for `r`: from a matching opening, else the cache, else (its
own legacy record) the recorded sent-to list. -/
def audienceFor (me : Me) (d : Digest) (r : Rec) (h : Held) : Option (Array Seat) :=
  match h.opening with
  | some o =>
    if openingMatches r.group r.author r.commit o then openingAudience me d r o
    else h.audience.or (ownSentTo me d r)
  | none => h.audience.or (ownSentTo me d r)

/-- `q` is seated in the audience the responder knows for stored record `r` at digest `d`. -/
def entitledHere (me : Me) (held : Std.ExtTreeMap Digest Held compare) (q : Query) (d : Digest)
    (r : Rec) : Bool :=
  (audienceFor me d r (held.getD d {})).any (seats · q.aci q.key)

/-- What `serveOpening` guarantees: the opening opens `r`; its own committed audience seats `q`,
or it has none and `r` is the responder's own live, undisowned record whose recorded sent-to list
seats `q`; and an export carries nothing ephemeral. -/
theorem serveOpening_spec {me : Me} {q : Query} {d : Digest} {r : Rec} {o : ByteArray}
    (h : serveOpening me q d r o = true) :
    openingMatches r.group r.author r.commit o = true ∧
      ((∃ aud, audienceOf o = some aud ∧ seats aud q.aci q.key = true) ∨
        (audienceOf o = none ∧ authorCopy me d r = true ∧
          ∃ aud, me.sentTo[d]? = some aud ∧ seats aud q.aci q.key = true)) ∧
      (q.forExport = true → ephemeral o = false) := by
  simp only [serveOpening, Bool.and_eq_true, Option.any_eq_true, Bool.not_eq_true',
    Bool.and_eq_false_iff] at h
  obtain ⟨⟨hm, aud, ha, hs⟩, hx⟩ := h
  refine ⟨hm, ?_, fun hexp => ?_⟩
  · simp only [openingAudience] at ha
    cases hao : audienceOf o with
    | some a =>
      rw [hao] at ha
      simp only [Option.some_or, Option.some.injEq] at ha
      exact .inl ⟨a, rfl, ha ▸ hs⟩
    | none =>
      rw [hao] at ha
      simp only [Option.none_or, ownSentTo] at ha
      split at ha
      · exact .inr ⟨rfl, by assumption, aud, ha, hs⟩
      · simp at ha
  · rcases hx with hx | hx
    · simp [hexp] at hx
    · exact hx

/-- For every stored record, the stored records that link it. -/
def linkedByMap (m : RecMap) : Std.ExtTreeMap Digest (List Digest) compare :=
  m.foldl (init := m.map fun _ _ => []) fun acc d r =>
    r.links.foldl (init := acc) fun acc l => acc.modify l (d :: ·)

/-- The stored records reachable from `q.since`. -/
def sinceReach (c : RawStore) (q : Query) : DigestSet :=
  walk (fun r => r.links.toList) c.map ∅ q.since.toList

/-- The records `q` is seated in and that are not reachable from `since`. -/
def visList (c : RawStore) (me : Me) (held : Std.ExtTreeMap Digest Held compare) (q : Query) :
    List Digest :=
  c.map.toList.filterMap fun (d, r) =>
    if entitledHere me held q d r && !(sinceReach c q).contains d then some d else none

/-- The stored records that reach a `vis` record: the walk backwards from them. -/
def upSet (c : RawStore) (me : Me) (held : Std.ExtTreeMap Digest Held compare) (q : Query) :
    DigestSet :=
  walk id (linkedByMap c.map) ∅ (visList c me held q)

/-- The digests linked by the stored records among `ds`. -/
def linksOf (c : RawStore) (ds : List Digest) : DigestSet :=
  ds.foldl (init := ∅) fun acc d =>
    match c.map[d]? with
    | some r => r.links.foldl (fun s l => s.insert l) acc
    | none => acc

/-- One item of a reply. -/
inductive Entry
  | addressed (r : Rec) (opening : Option ByteArray) (authorCopy : Bool)
  | after (r : Rec)
  | boundary (d : Digest)

/-- The reply to `q`. In per-digest mode, an entry for each wanted digest only, and content for a
wanted digest `q` is seated in whatever `since` says (`since` shapes structure, never content). -/
def serve (c : RawStore) (me : Me) (held : Std.ExtTreeMap Digest Held compare) (q : Query) :
    List Entry :=
  let up := upSet c me held q
  let sr := sinceReach c q
  let linkedByUp := linksOf c up.toList
  let linkedAny := linksOf c (c.map.toList.map (·.1))
  let perDigest := q.wanted.isSome
  let want : Digest → Bool := fun d => (q.wanted.map (·.contains d)).getD true
  let fromRecords := c.map.toList.filterMap fun (d, r) =>
    if !want d then none
    else if entitledHere me held q d r && (perDigest || !sr.contains d) then
      some (.addressed r ((held.getD d {}).opening.filter (serveOpening me q d r))
        (authorCopy me d r))
    else if up.contains d then some (.after r)
    else if perDigest || linkedByUp.contains d || !linkedAny.contains d then some (.boundary d)
    else none
  let fromBoundary := me.boundary.toList.filterMap fun d =>
    if want d && !c.map.contains d &&
        (perDigest || linkedByUp.contains d || !linkedAny.contains d) then
      some (.boundary d)
    else none
  fromRecords ++ fromBoundary

/-! ## What the reply may contain -/

theorem mem_map_toList {c : RawStore} {d : Digest} {r : Rec} (h : (d, r) ∈ c.map.toList) :
    c.map[d]? = some r :=
  Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some.1 h

/-- Every addressed entry: a stored record; an author copy only if the responder wrote it, holds
it `live` and has not disowned it; an opening only if it opens the record, its own committed
audience seats the requester's ACI and key (or it has none and the record is the responder's own,
whose recorded sent-to list seats the requester), and (export) it is not ephemeral. -/
theorem serve_addressed {c : RawStore} {me : Me} {held : Std.ExtTreeMap Digest Held compare}
    {q : Query} {r : Rec} {o : Option ByteArray} {ac : Bool}
    (he : Entry.addressed r o ac ∈ serve c me held q) :
    ∃ d : Digest, c.map[d]? = some r ∧
      (ac = true → r.author = me.aci ∧ me.live.contains d = true ∧ me.disown.contains d = false) ∧
      ∀ op, o = some op → serveOpening me q d r op = true := by
  simp only [serve, List.mem_append, List.mem_filterMap] at he
  rcases he with ⟨⟨d, r'⟩, hmem, hf⟩ | ⟨d, -, hf⟩
  · have hget := mem_map_toList hmem
    split at hf
    · simp at hf
    · split at hf
      · simp only [Option.some.injEq, Entry.addressed.injEq] at hf
        obtain ⟨rfl, rfl, rfl⟩ := hf
        refine ⟨d, hget, ?_, ?_⟩
        · intro hac
          simp only [authorCopy, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hac
          exact ⟨hac.1.1, hac.1.2, hac.2⟩
        · intro op hop
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

/-- **Content goes only where its author sent it.** Every opening in a reply to `q` opens a stored
record (so its audience is the one the author committed), and that audience seats `q.aci` with the
tag of `q.key`. The one exception is the author's own pre-upgrade record, which has no field 201:
then the responder is its author, holds it `live`, has not disowned it, and its recorded sent-to
list seats `q`. No author shortcut, no audience cache, no `since`. -/
theorem serve_content {c : RawStore} {me : Me} {held : Std.ExtTreeMap Digest Held compare}
    {q : Query} {r : Rec} {o : Option ByteArray} {ac : Bool}
    (he : Entry.addressed r o ac ∈ serve c me held q) :
    ∃ d : Digest, c.map[d]? = some r ∧
      ∀ op, o = some op → openingMatches r.group r.author r.commit op = true ∧
        ((∃ aud, audienceOf op = some aud ∧ seats aud q.aci q.key = true) ∨
          (audienceOf op = none ∧ authorCopy me d r = true ∧
            ∃ aud, me.sentTo[d]? = some aud ∧ seats aud q.aci q.key = true)) := by
  obtain ⟨d, hget, -, hop⟩ := serve_addressed he
  exact ⟨d, hget, fun op h => ⟨(serveOpening_spec (hop op h)).1, (serveOpening_spec (hop op h)).2.1⟩⟩

/-- **An author copy is the author's own.** -/
theorem serve_authorCopy {c : RawStore} {me : Me} {held : Std.ExtTreeMap Digest Held compare}
    {q : Query} {r : Rec} {o : Option ByteArray}
    (he : Entry.addressed r o true ∈ serve c me held q) :
    ∃ d : Digest, c.map[d]? = some r ∧ r.author = me.aci ∧ me.live.contains d = true ∧
      me.disown.contains d = false := by
  obtain ⟨d, hget, hac, -⟩ := serve_addressed he
  exact ⟨d, hget, hac rfl⟩

/-- **Exports carry no disappearing or view-once content.** -/
theorem serve_export {c : RawStore} {me : Me} {held : Std.ExtTreeMap Digest Held compare}
    {q : Query} {r : Rec} {op : ByteArray} {ac : Bool} (hx : q.forExport = true)
    (he : Entry.addressed r (some op) ac ∈ serve c me held q) : ephemeral op = false := by
  obtain ⟨d, -, -, hop⟩ := serve_addressed he
  exact (serveOpening_spec (hop op rfl)).2.2 hx

/-- **Noninterference, the converse of `serve_content`.** Every held opening that opens its stored
record, whose own committed audience seats `q` and that passes the export check, is in the reply:
in a catch-up when it is not reachable from `since`, in a per-digest repair when it is wanted.
With `serve_content`, the content of a reply is exactly that set. It depends on the store, the held
openings and `q` (`aci`, `key`, `since`, `wanted`, `forExport`), and on nothing else: not the
audience cache, not the responder's provenance, not the structure entries. `q.key` is
server-influenceable (TOFU); the host seals the reply to it (JOIN_PLAN §4.3). -/
theorem serve_content_complete {c : RawStore} {me : Me} {held : Std.ExtTreeMap Digest Held compare}
    {q : Query} {d : Digest} {r : Rec} {op : ByteArray}
    (hget : c.map[d]? = some r) (hop : (held.getD d {}).opening = some op)
    (hs : serveOpening me q d r op = true)
    (hw : (q.wanted.map (·.contains d)).getD true = true)
    (hsr : q.wanted.isSome = true ∨ (sinceReach c q).contains d = false) :
    ∃ ac, Entry.addressed r (some op) ac ∈ serve c me held q := by
  have hm : openingMatches r.group r.author r.commit op = true := (serveOpening_spec hs).1
  have hent : entitledHere me held q d r = true := by
    simp only [serveOpening, Bool.and_eq_true] at hs
    simp only [entitledHere, audienceFor, hop, hm, ite_true]
    exact hs.1.2
  refine ⟨authorCopy me d r, ?_⟩
  simp only [serve, List.mem_append, List.mem_filterMap]
  refine .inl ⟨(d, r), Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some.2 hget, ?_⟩
  have hcond : (entitledHere me held q d r && (q.wanted.isSome || !(sinceReach c q).contains d)) =
      true := by
    rcases hsr with h | h <;> simp [hent, h]
  simp only [hw, Bool.not_true, Bool.false_eq_true, ite_false, hcond, ite_true, hop,
    Option.filter, hs]

/-- **Structure without content** goes only for stored records in the walk back from the records
`q` is seated in and that are not reachable from `since`. -/
theorem serve_after {c : RawStore} {me : Me} {held : Std.ExtTreeMap Digest Held compare}
    {q : Query} {r : Rec} (he : Entry.after r ∈ serve c me held q) :
    ∃ d : Digest, c.map[d]? = some r ∧ d ∈ upSet c me held q := by
  simp only [serve, List.mem_append, List.mem_filterMap] at he
  rcases he with ⟨⟨d, r'⟩, hmem, hf⟩ | ⟨d, -, hf⟩
  · have hget := mem_map_toList hmem
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

/-- **A boundary digest hides nothing sent to `q`.** It is a stored record outside the walk (so it
reaches no record `q` is seated in beyond `since`), and if `q` is seated in it, this is a catch-up
and `q` already reaches it from `since`; or it is a digest of the responder's own boundary. -/
theorem serve_boundary {c : RawStore} {me : Me} {held : Std.ExtTreeMap Digest Held compare}
    {q : Query} {d : Digest} (he : Entry.boundary d ∈ serve c me held q) :
    (∃ r, c.map[d]? = some r ∧ d ∉ upSet c me held q ∧
      (entitledHere me held q d r = true → q.wanted = none ∧ (sinceReach c q).contains d = true)) ∨
    (me.boundary.contains d = true ∧ c.map.contains d = false) := by
  simp only [serve, List.mem_append, List.mem_filterMap] at he
  rcases he with ⟨⟨d', r⟩, hmem, hf⟩ | ⟨d', hmem, hf⟩
  · have hget := mem_map_toList hmem
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

end Serve
end Zrdt

#print axioms Zrdt.Serve.serve_content
#print axioms Zrdt.Serve.serveOpening_spec
#print axioms Zrdt.Serve.serve_authorCopy
#print axioms Zrdt.Serve.serve_export
#print axioms Zrdt.Serve.serve_after
#print axioms Zrdt.Serve.serve_boundary
#print axioms Zrdt.Serve.serve_content_complete
