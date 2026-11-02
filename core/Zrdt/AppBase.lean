import Zrdt.AppBase.Wire

/-!
# The apps' shared base (docs/apps/BUILD_M1.md §B, §C.1)

**Owner: lane base.** Lanes torrent and git import this module and never edit it; a change to a
layout fixed here goes through lane base (BUILD_M1 §D).

This module holds what the two apps share, without Mathlib:

- the constants: protocol 5, app tags, channel names, field numbers, domain tags, limits;
- **app messages** (`AppHeader`, `appMessage`, `appHeader`, `appOf`): the committed bytes of a
  channel record, `[201 audience] [210 app] [211 channel] [212 body] [215 descriptor]?
  [216 pointers]?`, in that order, each once (215 and 216 at most once), canonical;
- **ids**: `channelId` (`"zrdtC1"`), `storeId` (`"zrdtT1"`), `pieceNonce` (`"zrdtN1"`);
- **piece stores**: the `Descriptor` (field 215, `"zrdtD1"`), the piece context `PieceCtx`, the
  piece and manifest messages, openings and records, `pieceOk`, `assembleOk`, and `bindCtx`, which
  turns an announcement record and its opening into a context;
- the daemon's protocol-5 state, `State`: the chats (protocol 4, unchanged), the piece stores and
  their contexts;
- the base ops (`Request`, `Reply`, `parse`, `run`): empty in the skeleton; lane base fills them
  in (BUILD_M1 §B.5: `CHANNEL`, `PIECES_BIND`, `PIECE_ACCEPT`, `PIECE_OPENING`,
  `PIECES_COMPLETE`, `ASSEMBLE`).

The definitions above the ops are the reference encodings of BUILD_M1 §B: the torrent and git
lanes code against them now. Their theorems (BUILD_M1 §C.1) are lane base's work; nothing here
is proved yet beyond the `#guard`s.
-/

namespace Zrdt.AppBase

open Proto (Table Chat)

/-! ## Constants -/

/-- The frame protocol of the apps. `Proto.protocolVersion` becomes this when lane base's ops
land (one edit in `Proto.lean`, by lane base); until then `VERSION` says 4 and every op from
`0x17` replies `UNKNOWN_OP`. -/
def protocolVersion5 : Nat := 5

/-- The torrent app's tag (field 210). -/
def appTorrent : ByteArray := "bt".toUTF8

/-- The git app's tag (field 210). SHA-256 repositories only. -/
def appGit : ByteArray := "git-sha256".toUTF8

/-- The torrent app's one channel per Signal group (field 211). -/
def channelTorrent : ByteArray := "files".toUTF8

/-- The git app's one channel per Signal group (field 211); the repository name is in the push
body, so every repository of a group shares one table (G-F1). -/
def channelGit : ByteArray := "repos".toUTF8

/-- Field numbers of the committed messages. 201 is `Serve.audienceField`. -/
def fieldAudience : Nat := 201
/-- App tag. -/
def fieldApp : Nat := 210
/-- Channel name. -/
def fieldChannel : Nat := 211
/-- App body. -/
def fieldBody : Nat := 212
/-- Descriptor (an announcement with a piece store). -/
def fieldDescriptor : Nat := 215
/-- Piece pointers, opaque to Lean. -/
def fieldPointers : Nat := 216
/-- Piece index (a varint). -/
def fieldPieceIndex : Nat := 220
/-- Piece bytes. -/
def fieldPieceBytes : Nat := 221
/-- The manifest's ordered piece digests. -/
def fieldOrdered : Nat := 225
/-- The app manifest. -/
def fieldManifest : Nat := 226

example : fieldAudience = Serve.audienceField := rfl

/-- Domain tag of channel ids. -/
def channelTag : ByteArray := "zrdtC1".toUTF8
/-- Domain tag of piece-store ids. -/
def storeTag : ByteArray := "zrdtT1".toUTF8
/-- Domain tag of piece and manifest nonces. -/
def nonceTag : ByteArray := "zrdtN1".toUTF8
/-- Tag that starts a descriptor. -/
def descriptorTag : ByteArray := "zrdtD1".toUTF8

/-- log₂ of the piece size the host uses: P = 1 MiB. -/
def pieceExp : Nat := 20
/-- log₂ of the piece size the vectors and tests use: 1 KiB, so a multi-piece stream fits in
`vectors.json`. A descriptor may name either; every check is the same. -/
def testPieceExp : Nat := 10
/-- The piece sizes M1 accepts. -/
def pieceExpOk (k : Nat) : Bool := k == pieceExp || k == testPieceExp
/-- At most N = 64 pieces. -/
def maxPieces : Nat := 64
/-- A stream holds at most 64 pieces: 64 MiB at the host's piece size. -/
def maxStream : Nat := maxPieces * 2 ^ pieceExp
/-- App tags and channel names: 1 to 64 bytes. -/
def maxTagLen : Nat := 64
/-- Body (212): at most 24 KiB. -/
def maxBody : Nat := 24 * 1024
/-- App manifest (226): at most 4 KiB. -/
def maxManifest : Nat := 4096
/-- Pointers (216): at most 16 KiB. -/
def maxPointers : Nat := 16 * 1024
/-- Descriptor (215): at most 8 KiB. A well-formed descriptor is at most 6199 bytes (55, 32 per
digest, the manifest), so the bound refuses none; it makes every field of a well-formed app
message read back (`appHeader_appMessage`). -/
def maxDescriptor : Nat := 8 * 1024
/-- Content 205, checked by the host before sending: at most 64 KiB. -/
def maxContent : Nat := 64 * 1024
/-- At most 8 pieces per repair request. -/
def maxRepair : Nat := 8
/-- The manifest's nonce index. -/
def manifestIndex : Nat := 2 ^ 32 - 1

/-- A SHA-256 collision: two different byte strings with one digest. Every collision disjunct of
the apps' theorems is this one (a record-digest collision is one, through `encode`). Advertised
statements spell it out, as `Serve.audience_bound` does. -/
def Sha256Collision : Prop := ∃ x y : ByteArray, x ≠ y ∧ sha256 x = sha256 y

/-! ## Protobuf writing

`varint`, `lenField`, `varintField` and `u64be` are in `Zrdt.AppBase.Wire` (`AppBase/Wire.lean`),
with the lemmas that read them back. -/

/-! ## App messages (BUILD_M1 §B.2) -/

/-- The committed fields of an app message (Content 205 without fields 15 and 200). -/
structure AppHeader where
  /-- Field 201: the audience, as `AUDIENCE` returns it. -/
  audience : ByteArray
  /-- Field 210: the app tag. -/
  app : ByteArray
  /-- Field 211: the channel name. -/
  channel : ByteArray
  /-- Field 212: the app body. -/
  body : ByteArray
  /-- Field 215: the descriptor of the announcement's piece store, if any. -/
  descriptor : Option ByteArray := none
  /-- Field 216: the piece pointers (`ZrdtPointers`), opaque to Lean. -/
  pointers : Option ByteArray := none
deriving DecidableEq

/-- The limits of BUILD_M1 §B.3, and an audience `ACCEPT` takes (`Serve.parseAudience`). -/
def AppHeader.wellFormed (h : AppHeader) : Bool :=
  (Serve.parseAudience h.audience).isSome && 1 ≤ h.app.size && h.app.size ≤ maxTagLen &&
    1 ≤ h.channel.size && h.channel.size ≤ maxTagLen && h.body.size ≤ maxBody &&
    h.descriptor.all (·.size ≤ maxDescriptor) && h.pointers.all (·.size ≤ maxPointers)

/-- The canonical committed bytes of an app message. -/
def appMessage (h : AppHeader) : ByteArray :=
  lenField fieldAudience h.audience ++ lenField fieldApp h.app ++ lenField fieldChannel h.channel ++
    lenField fieldBody h.body ++ (h.descriptor.map (lenField fieldDescriptor ·)).getD .empty ++
    (h.pointers.map (lenField fieldPointers ·)).getD .empty

/-- Read committed bytes as an app message: exactly the fields 201, 210, 211, 212, then 215 and
216 at most once each, in that order, all length-delimited, well-formed, and written exactly as
`appMessage` writes them. `none` for anything else (a chat message, a piece, a manifest). -/
def appHeader (m : ByteArray) : Option AppHeader := do
  let fs ← fields m
  let vs ← fs.toList.mapM fun f => do pure (f.num, ← Serve.fieldValue m f)
  let h : AppHeader ← match vs with
    | [(201, a), (210, p), (211, c), (212, b)] => pure ⟨a, p, c, b, none, none⟩
    | [(201, a), (210, p), (211, c), (212, b), (215, d)] => pure ⟨a, p, c, b, some d, none⟩
    | [(201, a), (210, p), (211, c), (212, b), (216, q)] => pure ⟨a, p, c, b, none, some q⟩
    | [(201, a), (210, p), (211, c), (212, b), (215, d), (216, q)] =>
      pure ⟨a, p, c, b, some d, some q⟩
    | _ => none
  guard (h.wellFormed && appMessage h == m)
  pure h

/-- The app message an opening commits to (its nonce dropped). -/
def appOf (o : ByteArray) : Option AppHeader := do
  let (_, m) ← splitOpening o
  appHeader m

namespace AppExamples
open Zrdt.Examples

/-- Alice's audience: Alice and Bob, both seated. -/
def aud : ByteArray :=
  Serve.writeAudience #[⟨alice, Serve.keyTag ⟨Array.replicate 33 1⟩⟩,
    ⟨⟨⟨Array.replicate 16 0xb0⟩, rfl⟩, Serve.keyTag ⟨Array.replicate 33 2⟩⟩]

/-- A torrent announcement header with a descriptor and pointers. -/
def hdr : AppHeader :=
  { audience := aud, app := appTorrent, channel := channelTorrent, body := "zbt1".toUTF8,
    descriptor := some ⟨#[1, 2, 3]⟩, pointers := some ⟨#[4, 5]⟩ }

end AppExamples

open AppExamples in
#guard appHeader (appMessage hdr) == some hdr
open AppExamples in
#guard appHeader (appMessage { hdr with descriptor := none }) ==
  some { hdr with descriptor := none }
open AppExamples in
-- No app tag, an empty channel name, or a byte left over: not an app message.
#guard appHeader (appMessage { hdr with app := .empty }) == none &&
  appHeader (appMessage { hdr with channel := .empty }) == none &&
  appHeader (appMessage hdr ++ ⟨#[0x08, 0x01]⟩) == none
open AppExamples in
-- The committed bytes of an app message are the message itself: `COMMIT` keeps it whole.
#guard committedBytes (appMessage hdr) == some (appMessage hdr)
open AppExamples in
#guard (appOf (Zrdt.Examples.nonce.bytes ++ appMessage hdr)) == some hdr

/-! ## Ids (BUILD_M1 §B.2) -/

/-- A SHA-256 output as a group id. -/
def hashToGroup (b : ByteArray) : GroupId := ⟨(sha256 b).bytes, (sha256 b).size_eq⟩

/-- The channel of app `app`, name `name`, in Signal group `g`:
SHA-256(`"zrdtC1"` ‖ g ‖ u8 |app| ‖ app ‖ u8 |name| ‖ name). Both are 1 to 64 bytes. -/
def channelId (g : GroupId) (app name : ByteArray) : GroupId :=
  hashToGroup (channelTag ++ g.bytes ++ Proto.Write.u8 app.size.toUInt8 ++ app ++
    Proto.Write.u8 name.size.toUInt8 ++ name)

/-- The piece store of an announcement: SHA-256(`"zrdtT1"` ‖ channel ‖ author ‖ store nonce). -/
def storeId (channel : GroupId) (author : Aci) (nonce : Nonce) : GroupId :=
  hashToGroup (storeTag ++ channel.bytes ++ author.bytes ++ nonce.bytes)

/-- The nonce of piece `i` (and of the manifest, at `manifestIndex`):
SHA-256(`"zrdtN1"` ‖ store nonce ‖ u32 i). Deterministic, so a responder rebuilds the opening. -/
def pieceNonce (nonce : Nonce) (i : Nat) : Nonce :=
  let d := sha256 (nonceTag ++ nonce.bytes ++ u32be i)
  ⟨d.bytes, d.size_eq⟩

/-- The commitment of committed bytes `m` (`Zrdt.commit` of a message that has no field 15 or
200). -/
def commitOf (g : GroupId) (a : Aci) (n : Nonce) (m : ByteArray) : Digest :=
  sha256 (commitTag ++ g.bytes ++ a.bytes ++ n.bytes ++ m)

/-! ## The descriptor (field 215, BUILD_M1 §B.2) -/

/-- An announcement's piece store: `"zrdtD1"` ‖ store nonce ‖ u64 L ‖ u8 k ‖ ordered (u32 N ‖ N
digests, index order) ‖ app manifest (`bytes`). -/
structure Descriptor where
  /-- 32 random bytes, committed in the announcement; salts the store id and piece nonces. -/
  nonce : Nonce
  /-- The stream length L. -/
  len : Nat
  /-- log₂ of the piece size: 20 (hosts) or 10 (vectors). -/
  exp : Nat
  /-- The piece digests in index order. -/
  ordered : Array Digest
  /-- The app manifest (field 226 of the manifest record). -/
  manifest : ByteArray

/-- The descriptor's bytes. -/
def Descriptor.write (d : Descriptor) : ByteArray :=
  descriptorTag ++ d.nonce.bytes ++ u64be d.len ++ Proto.Write.u8 d.exp.toUInt8 ++
    Proto.Write.digests d.ordered ++ Proto.Write.bytes d.manifest

/-- A `u64`. -/
def readU64 : Proto.Parser Nat := do
  let hi ← Proto.Parser.u32
  let lo ← Proto.Parser.u32
  pure (hi * 2 ^ 32 + lo)

/-- Read a descriptor; every byte must be used. -/
def Descriptor.parse (b : ByteArray) : Option Descriptor :=
  Proto.Parser.run (do
    let t ← Proto.Parser.take 6
    if t != descriptorTag then failure
    let n ← Proto.Parser.nonce
    let len ← readU64
    let k ← Proto.Parser.u8
    let ds ← Proto.Parser.digests
    let m ← Proto.Parser.bytes
    pure ⟨n, len, k.toNat, ds, m⟩) b 0

/-- The number of pieces of a stream of length `len` in pieces of 2^k bytes: ⌈len / 2^k⌉. -/
def pieceCount (k len : Nat) : Nat := (len + 2 ^ k - 1) / 2 ^ k

/-- M1's limits: k ∈ {20, 10}, 1 ≤ L ≤ 64 · 2^k, N = ⌈L/2^k⌉ digests with no repeat, manifest
≤ 4 KiB. -/
def Descriptor.wellFormed (d : Descriptor) : Bool :=
  pieceExpOk d.exp && 1 ≤ d.len && d.len ≤ maxPieces * 2 ^ d.exp &&
    d.ordered.size == pieceCount d.exp d.len &&
    (canonicalLinks d.ordered).size == d.ordered.size && d.manifest.size ≤ maxManifest

/-! ## Piece contexts, pieces and the manifest (BUILD_M1 §B.2) -/

/-- What `zrdtd` knows about one piece store, from its announcement A (`bindCtx`). In memory
only; after a restart the host binds again and re-runs `PIECE_ACCEPT`. -/
structure PieceCtx where
  /-- A's record digest (the host's piece key names it, T-m10). -/
  announcement : Digest
  /-- A's group: the channel id. -/
  channel : GroupId
  /-- A's author. -/
  author : Aci
  /-- A's app message. -/
  header : AppHeader
  /-- A's audience, parsed. -/
  seats : Array Serve.Seat
  /-- A's descriptor. -/
  desc : Descriptor

/-- The piece store's group. -/
def PieceCtx.storeId (c : PieceCtx) : GroupId := AppBase.storeId c.channel c.author c.desc.nonce

/-- N. -/
def PieceCtx.count (c : PieceCtx) : Nat := c.desc.ordered.size

/-- The length of piece `i` of a stream of length `len` in pieces of 2^k bytes: 2^k, except the
last. -/
def pieceLen (k len i : Nat) : Nat := min (2 ^ k) (len - i * 2 ^ k)

/-- Piece `i` of stream `s`, in pieces of 2^k bytes (`extract` clamps at the end). -/
def slice (k : Nat) (s : ByteArray) (i : Nat) : ByteArray := s.extract (i * 2 ^ k) ((i + 1) * 2 ^ k)

/-- A piece's committed bytes: `[201 audience] [220 varint i] [221 bytes]`. -/
def pieceMessage (aud : ByteArray) (i : Nat) (b : ByteArray) : ByteArray :=
  lenField fieldAudience aud ++ varintField fieldPieceIndex i ++ lenField fieldPieceBytes b

/-- Piece `i`'s opening: its nonce, then its committed bytes. Only `zrdtd` builds it. -/
def pieceOpening (c : PieceCtx) (i : Nat) (b : ByteArray) : ByteArray :=
  (pieceNonce c.desc.nonce i).bytes ++ pieceMessage c.header.audience i b

/-- Piece `i`'s record: (storeId, its commitment, no links, A's author). -/
def pieceRecord (c : PieceCtx) (i : Nat) (b : ByteArray) : Rec :=
  Rec.make c.storeId (commitOf c.storeId c.author (pieceNonce c.desc.nonce i)
    (pieceMessage c.header.audience i b)) #[] c.author

/-- The manifest's committed bytes: `[201 audience] [225 ordered digests] [226 app manifest]`. -/
def manifestMessage (c : PieceCtx) : ByteArray :=
  lenField fieldAudience c.header.audience ++ lenField fieldOrdered (linksBytes c.desc.ordered) ++
    lenField fieldManifest c.desc.manifest

/-- The manifest's opening. -/
def manifestOpening (c : PieceCtx) : ByteArray :=
  (pieceNonce c.desc.nonce manifestIndex).bytes ++ manifestMessage c

/-- The manifest record F: (storeId, its commitment, links = the N piece digests, A's author).
A complete store has heads {F}: its compare code. -/
def manifestRecord (c : PieceCtx) : Rec :=
  Rec.make c.storeId (commitOf c.storeId c.author (pieceNonce c.desc.nonce manifestIndex)
    (manifestMessage c)) c.desc.ordered c.author

/-- `b` is piece `i` of the context: i < N, |b| is piece i's length, and the record built from it
has the digest A committed for index i. -/
def pieceOk (c : PieceCtx) (i : Nat) (b : ByteArray) : Bool :=
  match c.desc.ordered[i]? with
  | none => false
  | some d => b.size == pieceLen c.desc.exp c.desc.len i && hashRecord (pieceRecord c i b) == d

/-- Stream `s` is the context's whole stream: length L, and every slice passes `pieceOk`. -/
def assembleOk (c : PieceCtx) (s : ByteArray) : Bool :=
  s.size == c.desc.len && (List.range c.count).all fun i => pieceOk c i (slice c.desc.exp s i)

namespace AppExamples
open Zrdt.Examples

/-- A 2.5 KiB stream: three pieces of 1 KiB (k = 10), the last one short. -/
def stream : ByteArray := ⟨(Array.range 2560).map (·.toUInt8)⟩

/-- A context for `stream`, built as `BT_BUILD` does: the digests come from the slices. -/
def ctx : PieceCtx :=
  let base : PieceCtx :=
    { announcement := Digest.zero, channel := channelId group appTorrent channelTorrent,
      author := alice, header := hdr, seats := (Serve.parseAudience aud).getD #[],
      desc := ⟨Zrdt.Examples.nonce, 2560, testPieceExp, #[], ⟨#[7]⟩⟩ }
  let ordered := (Array.range 3).map fun i =>
    hashRecord (pieceRecord base i (slice testPieceExp stream i))
  { base with desc := { base.desc with ordered := ordered } }

end AppExamples

open AppExamples in
#guard ctx.desc.wellFormed && assembleOk ctx stream && pieceOk ctx 2 (slice testPieceExp stream 2) &&
  (slice testPieceExp stream 2).size == 512 && !pieceOk ctx 1 (slice testPieceExp stream 2) &&
  !assembleOk ctx (stream.set! 5 0) &&
  (Descriptor.parse ctx.desc.write).map (·.write) == some ctx.desc.write
open AppExamples in
-- Piece and manifest openings are not app messages; their committed bytes are kept whole.
#guard appOf (pieceOpening ctx 0 (slice testPieceExp stream 0)) == none &&
  appOf (manifestOpening ctx) == none &&
  committedBytes (pieceMessage aud 0 (slice testPieceExp stream 0)) ==
    some (pieceMessage aud 0 (slice testPieceExp stream 0)) &&
  Serve.audienceOf (pieceOpening ctx 1 (slice testPieceExp stream 1)) == Serve.parseAudience aud

/-! ## Binding an announcement (BUILD_M1 §B.5, `PIECES_BIND`) -/

/-- Why `PIECES_BIND` refuses (the reason byte of `BAD_APP`). -/
inductive BadApp
  /-- 1: A is not stored in the channel, or the channel is not (Signal group, app, name). -/
  | notStored
  /-- 2: the opening does not match A. -/
  | opening
  /-- 3: not a canonical app message of this app and channel. -/
  | notApp
  /-- 4: A's audience does not seat this device (own ACI under own key tag, T-m12). -/
  | notSeated
  /-- 5: no descriptor, or one that does not parse or breaks M1's limits. -/
  | descriptor
  /-- 6: an author op's input breaks the limits (stream length, audience, pointers, sizes). -/
  | limits
  /-- 7: the piece key's context is another app's (e.g. `BT_FILE` on a git push's store). -/
  | wrongApp
deriving DecidableEq, Repr

/-- The reason byte. -/
def BadApp.byte : BadApp → UInt8
  | .notStored => 1 | .opening => 2 | .notApp => 3 | .notSeated => 4 | .descriptor => 5
  | .limits => 6 | .wrongApp => 7

/-- The context of announcement `A` with opening `o`, for app `app` in Signal group `sg`: the
opening matches A, commits a canonical app message of `app` whose channel id (from `sg`, `app`
and the committed channel name) is A's group, and carries a well-formed descriptor. A function of
(A, o) once it succeeds, so two devices that bind one announcement get one context
(`bindCtx_unique`, BUILD_M1 §C.1). The checks that need the daemon's state (A stored in the
channel, the seat of this device, the piece key free) are `PIECES_BIND`'s. -/
def bindCtx (sg : GroupId) (app : ByteArray) (A : Rec) (o : ByteArray) :
    Except BadApp PieceCtx := do
  unless openingMatches A.group A.author A.commit o do throw .opening
  let some h := appOf o | throw .notApp
  unless h.app == app && channelId sg h.app h.channel == A.group do throw .notApp
  let some db := h.descriptor | throw .descriptor
  let some d := Descriptor.parse db | throw .descriptor
  unless d.wellFormed do throw .descriptor
  let some seats := Serve.parseAudience h.audience | throw .notApp
  -- announcement, channel, author, header, seats, desc
  pure ⟨hashRecord A, A.group, A.author, h, seats, d⟩

/-! ## The daemon's protocol-5 state -/

/-- What `zrdtd` holds under protocol 5. `chats` is protocol 4's table, unchanged. `pieces` holds
the piece stores (a closed store each, in the same `Chat` shape, so `SERVE` and the other
read-only protocol-4 ops run on them unchanged) and `ctxs` their contexts, under the same keys.
Only lane base's ops write `pieces` and `ctxs` (`PIECES_BIND` creates, `PIECE_ACCEPT` and
`PIECES_COMPLETE` add, `CLOSE` removes); the torrent and git ops only read. -/
structure State where
  /-- The chats and channels (protocol 4). -/
  chats : Table := {}
  /-- The piece stores. -/
  pieces : Table := {}
  /-- Their contexts. -/
  ctxs : Std.HashMap String PieceCtx := {}

instance : Inhabited State := ⟨{}⟩

/-! ## The base ops (lane base; BUILD_M1 §B.5)

`CHANNEL` `0x17`, `PIECES_BIND` `0x18`, `PIECE_ACCEPT` `0x19`, `PIECE_OPENING` `0x1A`,
`PIECES_COMPLETE` `0x1B`, `ASSEMBLE` `0x1C`; `0x1D`-`0x1F` reserved (`UNKNOWN_OP`). Byte layouts:
the section `[lane base]` of the header of `Zrdt.Proto`. -/

/-- A base request. -/
inductive Request
  /-- `CHANNEL`: the channel id of app `app`, name `name`, in Signal group `sg`. -/
  | channel (sg : GroupId) (app name : String)
  /-- `PIECES_BIND`: bind announcement `A` (its encoding, and its opening) of the channel open
  under `chan`, for app `app` in Signal group `sg`, on this device (`me` under its own key
  `myKey`); the piece store opens under `key`. -/
  | piecesBind (key chan : String) (sg : GroupId) (app : String) (me : Aci) (myKey : ByteArray)
      (announcement opening : ByteArray)
  /-- `PIECE_ACCEPT`: piece `i` of the store under `key`. -/
  | pieceAccept (key : String) (i : Nat) (piece : ByteArray)
  /-- `PIECE_OPENING`: the opening of piece `i`, for `SERVE`'s `held` list. -/
  | pieceOpening (key : String) (i : Nat) (piece : ByteArray)
  /-- `PIECES_COMPLETE`: accept the manifest F. -/
  | piecesComplete (key : String)
  /-- `ASSEMBLE`: is `stream` the whole stream? -/
  | assemble (key : String) (stream : ByteArray)

/-- The op byte and name of each request (`Proto.baseOpNames`). -/
def Request.op : Request → UInt8 × String
  | .channel .. => (0x17, "CHANNEL") | .piecesBind .. => (0x18, "PIECES_BIND")
  | .pieceAccept .. => (0x19, "PIECE_ACCEPT") | .pieceOpening .. => (0x1A, "PIECE_OPENING")
  | .piecesComplete .. => (0x1B, "PIECES_COMPLETE") | .assemble .. => (0x1C, "ASSEMBLE")

/-- A base reply. -/
inductive Reply
  /-- `CHANNEL` → `OK`: the channel id. -/
  | channel (g : GroupId)
  /-- `PIECES_BIND` → `OK`: the context the store was bound to. -/
  | bound (c : PieceCtx)
  /-- `PIECE_ACCEPT` → `OK`: the piece record's digest. -/
  | digest (d : Digest)
  /-- `PIECE_OPENING` → `OK`: the piece's opening. -/
  | opening (o : ByteArray)
  /-- `PIECES_COMPLETE`: what `ACCEPT` says for F (`OK`, `MISSING`, ...), and `PIECE_ACCEPT` if
  the store refuses a checked piece (`COLLISION` only, which needs a SHA-256 collision). -/
  | accept (r : Rec) (res : AcceptResult)
  /-- `ASSEMBLE` → `OK`. -/
  | ok
  /-- `BAD_PIECE`: empty (`PIECE_ACCEPT`, `PIECE_OPENING`), or the first bad index
  (`ASSEMBLE`). -/
  | badPiece (i : Option Nat)
  /-- `BAD_APP` with its reason. -/
  | badApp (r : BadApp)
  /-- Another status with an empty body: `NO_CHAT`, `CHAT_OPEN`, `MALFORMED`. -/
  | code (c : Proto.Code)

/-- The request's payload (op byte first). -/
def Request.write (q : Request) : ByteArray :=
  Proto.Write.u8 q.op.1 ++
    match q with
    | .channel sg p n => sg.bytes ++ Proto.Write.str p ++ Proto.Write.str n
    | .piecesBind key chan sg p me k aB o =>
      Proto.Write.str key ++ Proto.Write.str chan ++ sg.bytes ++ Proto.Write.str p ++ me.bytes ++ k ++
        Proto.Write.bytes aB ++ Proto.Write.bytes o
    | .pieceAccept key i b | .pieceOpening key i b => Proto.Write.str key ++ u32be i ++ Proto.Write.bytes b
    | .piecesComplete key => Proto.Write.str key
    | .assemble key st => Proto.Write.str key ++ Proto.Write.bytes st

/-- The reply's payload (status byte first). -/
def Reply.write : Reply → ByteArray
  | .channel g => Proto.Code.ok.write ++ g.bytes
  | .bound c =>
    Proto.Code.ok.write ++ u64be c.desc.len ++ Proto.Write.u8 c.desc.exp.toUInt8 ++
      Proto.Write.digests c.desc.ordered ++ Proto.Write.bytes c.header.body ++ Proto.Write.bytes c.desc.manifest ++
      Proto.Write.bytes (c.header.pointers.getD .empty)
  | .digest d => Proto.Code.ok.write ++ d.bytes
  | .opening o => Proto.Code.ok.write ++ Proto.Write.bytes o
  | .accept r res => (Proto.Reply.accept r res).write
  | .ok => Proto.Code.ok.write
  | .badPiece none => Proto.Code.badPiece.write
  | .badPiece (some i) => Proto.Code.badPiece.write ++ u32be i
  | .badApp r => Proto.Code.badApp.write ++ Proto.Write.u8 r.byte
  | .code c => c.write

open Proto.Parser in
/-- The body parser of base op `op` (`0x17`-`0x1F`); `none`: not a base op. -/
def parse : UInt8 → Option (Proto.Parser Request)
  | 0x17 => some (.channel <$> group <*> str <*> str)
  | 0x18 => some (.piecesBind <$> str <*> str <*> group <*> str <*> aci <*> key <*> bytes <*> bytes)
  | 0x19 => some (.pieceAccept <$> str <*> u32 <*> bytes)
  | 0x1A => some (.pieceOpening <$> str <*> u32 <*> bytes)
  | 0x1B => some (.piecesComplete <$> str)
  | 0x1C => some (.assemble <$> str <*> bytes)
  | _ => none

-- `Request.op` agrees with `Proto.baseOpNames`.
#guard [Request.channel GroupId.zero "" "", .piecesBind "" "" GroupId.zero "" Aci.zero .empty .empty
    .empty, .pieceAccept "" 0 .empty, .pieceOpening "" 0 .empty, .piecesComplete "",
    .assemble "" .empty].all fun q => Proto.baseOpNames.lookup q.op.1 == some q.op.2
#guard Proto.baseOpNames.length == 6

/-- An app tag or channel name: 1 to 64 bytes. -/
def tagOk (b : ByteArray) : Bool := 1 ≤ b.size && b.size ≤ maxTagLen

/-- `PIECES_BIND`. In order: `NO_CHAT` (no channel under `chan`), `CHAT_OPEN` (`key` in use, as a
chat or a piece store), `MALFORMED` (`aB` is not a record), `BAD_APP` 1 (A is not stored in the
channel), `bindCtx`'s `BAD_APP` 2, 3 or 5, `BAD_APP` 4 (A's audience does not seat `me` under the
tag of `k`, T-m12). On success, an empty closed store with group `storeId` under `key`, and the
context. -/
def bindPieces (s : State) (key chan : String) (sg : GroupId) (app : String) (me : Aci)
    (k aB o : ByteArray) : Reply × State :=
  match s.chats[chan]? with
  | none => (.code .noChat, s)
  | some ch =>
    if s.chats.contains key || s.pieces.contains key then (.code .chatOpen, s)
    else
      match decode aB with
      | none => (.code .malformed, s)
      | some A =>
        if !ch.store.has (hashRecord A) then (.badApp .notStored, s)
        else
          match bindCtx sg app.toUTF8 A o with
          | .error e => (.badApp e, s)
          | .ok c =>
            if !Serve.seats c.seats me k then (.badApp .notSeated, s)
            else
              let fresh : Proto.Chat := { store := .closed (.empty c.storeId) }
              (.bound c, { s with pieces := s.pieces.insert key fresh, ctxs := s.ctxs.insert key c })

/-- Put record `r` in the piece store `ch` under `key`, with its audience `c.seats`: what `ACCEPT`
says, and the new state when it is accepted (otherwise nothing changes). -/
def acceptInto (s : State) (key : String) (ch : Proto.Chat) (c : PieceCtx) (r : Rec) :
    AcceptResult × State :=
  match ch.store.accept r with
  | (.accepted d, st) =>
    let ch' : Proto.Chat := { store := st, audiences := ch.audiences.insert d c.seats }
    (.accepted d, { s with pieces := s.pieces.insert key ch' })
  | (res, _) => (res, s)

/-- `PIECE_ACCEPT`: a piece that passes `pieceOk` goes into the store with A's audience; any other
gets `BAD_PIECE` and changes nothing. -/
def acceptPiece (s : State) (key : String) (i : Nat) (b : ByteArray) : Reply × State :=
  match s.ctxs[key]?, s.pieces[key]? with
  | some c, some ch =>
    if pieceOk c i b then
      match acceptInto s key ch c (pieceRecord c i b) with
      | (.accepted d, s') => (.digest d, s')
      | (res, s') => (.accept (pieceRecord c i b) res, s')
    else (.badPiece none, s)
  | _, _ => (.code .noChat, s)

/-- `PIECE_OPENING`: the opening of a piece that passes `pieceOk`. -/
def openingOf (s : State) (key : String) (i : Nat) (b : ByteArray) : Reply :=
  match s.ctxs[key]? with
  | some c => if pieceOk c i b then .opening (pieceOpening c i b) else .badPiece none
  | none => .code .noChat

/-- `PIECES_COMPLETE`: `ACCEPT` of the manifest F, derived from the context (so it always has
A's audience and descriptor), with A's audience recorded when it is accepted. -/
def complete (s : State) (key : String) : Reply × State :=
  match s.ctxs[key]?, s.pieces[key]? with
  | some c, some ch =>
    let (res, s') := acceptInto s key ch c (manifestRecord c)
    (.accept (manifestRecord c) res, s')
  | _, _ => (.code .noChat, s)

/-- The first index at which `stream` is not the context's stream: N if its length is not L,
otherwise the first slice that fails `pieceOk`; `none` if it is the stream (`firstBad_none`). -/
def firstBad (c : PieceCtx) (stream : ByteArray) : Option Nat :=
  if stream.size != c.desc.len then some c.count
  else (List.range c.count).find? fun i => !pieceOk c i (slice c.desc.exp stream i)

/-- `ASSEMBLE`. -/
def assembleReply (s : State) (key : String) (stream : ByteArray) : Reply :=
  match s.ctxs[key]? with
  | some c =>
    match firstBad c stream with
    | none => .ok
    | some i => .badPiece (some i)
  | none => .code .noChat

/-- Carry out a base request. The only protocol-5 code that changes `State`: `PIECES_BIND`
creates a piece store and its context, `PIECE_ACCEPT` and `PIECES_COMPLETE` add to it (`CLOSE` of
a piece key, in `Zrdt.Apps`, removes both). -/
def run (s : State) : Request → Reply × State
  | .channel sg p n =>
    (if tagOk p.toUTF8 && tagOk n.toUTF8 then .channel (channelId sg p.toUTF8 n.toUTF8)
      else .badApp .limits, s)
  | .piecesBind key chan sg p me k aB o => bindPieces s key chan sg p me k aB o
  | .pieceAccept key i b => acceptPiece s key i b
  | .pieceOpening key i b => (openingOf s key i b, s)
  | .piecesComplete key => complete s key
  | .assemble key st => (assembleReply s key st, s)

/-! ## A worked announcement (the vectors' `pieces` session, and the examples below)

Alice announces the 2.5 KiB `AppExamples.stream` (three pieces at k = 10) to Signal group
`Examples.group` in its torrent channel `chanBt`, for herself, Bob and Carol under their keys and
Mallory with no key (not seated). `annA` is the record, `openA` its opening, and binding them gives
`ctxA`. `annBare` is an announcement of the same channel without a descriptor. -/

namespace AppExamples
open Zrdt.Examples
open Serve.Examples (keyAlice keyBob keyCarol mallory audienceOfKeys)

/-- The Signal group's torrent channel. -/
def chanBt : GroupId := channelId group appTorrent channelTorrent

/-- The members as `AUDIENCE` gets them: Alice, Bob and Carol under their keys, Mallory with
none. -/
def membersA : Array (Aci × Option ByteArray) :=
  #[(alice, some keyAlice), (bob, some keyBob), (carol, some keyCarol), (mallory, none)]

/-- The announcement's audience (`AUDIENCE`'s value for `membersA`). -/
def audA : ByteArray := Serve.writeAudience (audienceOfKeys membersA.toList)

/-- The store nonce. -/
def storeNonce : Nonce := ⟨⟨Array.replicate 32 0x5d⟩, rfl⟩

/-- A's commitment nonce. -/
def nonceA : Nonce := ⟨⟨Array.replicate 32 0xa5⟩, rfl⟩

/-- The app manifest (opaque to the base). -/
def manifestA : ByteArray := "base manifest".toUTF8

/-- A's app message before its descriptor. -/
def hdrA0 : AppHeader :=
  { audience := audA, app := appTorrent, channel := channelTorrent, body := "zbt1".toUTF8 }

/-- The context before its digests: everything a piece record depends on. -/
def ctxA0 : PieceCtx :=
  { announcement := Digest.zero, channel := chanBt, author := alice, header := hdrA0,
    seats := audienceOfKeys membersA.toList,
    desc := ⟨storeNonce, stream.size, testPieceExp, #[], manifestA⟩ }

/-- The descriptor: the digests of the slices of `stream`. -/
def descA : Descriptor :=
  { ctxA0.desc with
    ordered := (Array.range 3).map fun i => hashRecord (pieceRecord ctxA0 i (slice 10 stream i)) }

/-- A's app message. -/
def hdrA : AppHeader := { hdrA0 with descriptor := some descA.write }

/-- A's committed bytes. -/
def msgA : ByteArray := appMessage hdrA

/-- A: the record. -/
def annA : Rec := Rec.make chanBt (commitOf chanBt alice nonceA msgA) #[] alice

/-- A's opening. -/
def openA : ByteArray := nonceA.bytes ++ msgA

/-- The context `PIECES_BIND` of A gives. -/
def ctxA : PieceCtx :=
  { announcement := hashRecord annA, channel := chanBt, author := alice, header := hdrA,
    seats := audienceOfKeys membersA.toList, desc := descA }

/-- An announcement with no descriptor (a nonce of its own). -/
def hdrBare : AppHeader := { hdrA0 with body := "bare".toUTF8 }

/-- Its record. -/
def annBare : Rec :=
  Rec.make chanBt (commitOf chanBt alice storeNonce (appMessage hdrBare)) #[] alice

/-- Its opening. -/
def openBare : ByteArray := storeNonce.bytes ++ appMessage hdrBare

/-- Piece `i` of `stream`. -/
def pieceA (i : Nat) : ByteArray := slice testPieceExp stream i

/-- A byte of `b` changed. -/
def flip (b : ByteArray) (k : Nat) : ByteArray := b.set! k (b[k]! ^^^ 0xff)

end AppExamples

open AppExamples in
-- A binds: the context is `ctxA`; its digests are the pieces'.
#guard (match bindCtx Examples.group appTorrent annA openA with
  | .ok c => c.announcement == ctxA.announcement && c.channel == ctxA.channel &&
      c.author == ctxA.author && c.header == ctxA.header && c.seats == ctxA.seats &&
      c.desc.write == ctxA.desc.write
  | .error _ => false)
open AppExamples in
-- Each refusal of `bindCtx`: another app, another Signal group, a wrong opening, no descriptor.
#guard [bindCtx Examples.group appGit annA openA, bindCtx Examples.otherGroup appTorrent annA openA,
    bindCtx Examples.group appTorrent annA openBare,
    bindCtx Examples.group appTorrent annBare openBare].map (fun
      | .error e => e.byte | .ok _ => 0) == [3, 3, 2, 5]
open AppExamples in
#guard descA.wellFormed && hdrA.wellFormed && assembleOk ctxA stream &&
  (List.range 3).all (fun i => pieceOk ctxA i (pieceA i)) && !pieceOk ctxA 1 (flip (pieceA 1) 3) &&
  !pieceOk ctxA 3 (pieceA 0) && firstBad ctxA (flip stream 1500) == some 1 &&
  firstBad ctxA (stream.extract 0 2000) == some 3 && firstBad ctxA stream == none &&
  Serve.seats ctxA.seats Examples.bob Serve.Examples.keyBob &&
  !Serve.seats ctxA.seats Serve.Examples.mallory Serve.Examples.keyMallory

/-! ## What the base guarantees (BUILD_M1 §C.1)

Every statement below is about the definitions above, the code `zrdtd` runs. The protobuf and
parser lemmas they use are in `Zrdt.AppBase.Wire`. -/

section Proofs
open Wire

/-! ### App messages read back, and mean one thing -/

/-- The fields of an app message after the audience, as (number, value). -/
def AppHeader.restPairs (h : AppHeader) : List (Nat × ByteArray) :=
  [(fieldApp, h.app), (fieldChannel, h.channel), (fieldBody, h.body)] ++
    (h.descriptor.map (fieldDescriptor, ·)).toList ++ (h.pointers.map (fieldPointers, ·)).toList

/-- The fields of an app message, as (number, value). -/
def AppHeader.pairs (h : AppHeader) : List (Nat × ByteArray) :=
  (fieldAudience, h.audience) :: h.restPairs

/-- Length-delimited fields. -/
def lens (ps : List (Nat × ByteArray)) : List Item := ps.map fun p => .len p.1 p.2

/-- An app message is its fields written one after another. -/
theorem appMessage_eq (h : AppHeader) : appMessage h = writeItems (lens h.pairs) := by
  obtain ⟨a, p, c, b, d, q⟩ := h
  cases d <;> cases q <;>
    simp [appMessage, AppHeader.pairs, AppHeader.restPairs, lens, writeItems, Item.write,
      ByteArray.append_assoc, ByteArray.append_empty]

/-- The fields of a well-formed app message read back: their numbers and sizes are in range. -/
theorem pairs_ok {h : AppHeader} (hw : h.wellFormed = true) :
    ∀ p ∈ h.pairs, (Item.len p.1 p.2).ok := by
  obtain ⟨a, pp, c, b, d, q⟩ := h
  simp only [AppHeader.wellFormed, Bool.and_eq_true, decide_eq_true_eq] at hw
  obtain ⟨⟨⟨⟨⟨⟨⟨ha, hp1⟩, hp2⟩, hc1⟩, hc2⟩, hb⟩, hd⟩, hq⟩ := hw
  obtain ⟨aud, haud⟩ := Option.isSome_iff_exists.mp ha
  have hasz := size_of_parseAudience haud
  simp only [Serve.maxAudience, maxTagLen, maxBody, maxDescriptor, maxPointers] at *
  intro x hx
  simp only [AppHeader.pairs, AppHeader.restPairs, List.mem_append, List.mem_cons,
    List.mem_nil_iff, or_false] at hx
  rcases hx with (rfl | ((rfl | rfl | rfl) | hx) | hx)
  all_goals first
    | (simp only [Item.ok, fieldAudience, fieldApp, fieldChannel, fieldBody]; omega)
    | skip
  · cases d with
    | none => simp at hx
    | some dv =>
      simp only [Option.map_some, Option.toList_some, List.mem_singleton] at hx
      subst hx
      simp [Option.all] at hd
      have := of_decide_eq_true hd
      simp only [Item.ok, fieldDescriptor]; omega
  · cases q with
    | none => simp at hx
    | some qv =>
      simp only [Option.map_some, Option.toList_some, List.mem_singleton] at hx
      subst hx
      simp [Option.all] at hq
      have := of_decide_eq_true hq
      simp only [Item.ok, fieldPointers]; omega

theorem lens_ok {ps : List (Nat × ByteArray)} (h : ∀ p ∈ ps, (Item.len p.1 p.2).ok) :
    ∀ it ∈ lens ps, it.ok := by
  intro it hit
  simp only [lens, List.mem_map] at hit
  obtain ⟨p, hp, rfl⟩ := hit
  exact h p hp

/-- `appHeader`'s values of the fields of a written message are the written values. -/
theorem mapM_fieldValue {m : ByteArray} : ∀ (ps : List (Nat × ByteArray)) (pos : Nat),
    (∀ p ∈ ps, (Item.len p.1 p.2).ok) → At m pos (writeItems (lens ps)) →
    (layout pos (lens ps)).mapM (fun f => do pure (f.num, ← Serve.fieldValue m f)) = some ps
  | [], _, _, _ => rfl
  | p :: ps, pos, ho, h => by
    simp only [lens, List.map_cons, writeItems, layout] at h ⊢
    rw [List.mapM_cons]
    have h1 := At.left h
    have h2 := At.right h
    simp only [Item.write] at h1
    simp only [Item.num]
    rw [fieldValue_len h1 (ho p (by simp))]
    have ih := mapM_fieldValue ps _ (fun x hx => ho x (by simp [hx])) h2
    simp only [lens, Option.bind_eq_bind, Option.pure_def] at ih ⊢
    simp [ih]

/-- **An app message reads back.** `appHeader` of the bytes `appMessage` writes for a well-formed
header is that header. -/
theorem appHeader_appMessage {h : AppHeader} (hw : h.wellFormed = true) :
    appHeader (appMessage h) = some h := by
  have hok := pairs_ok hw
  have hfs : fields (appMessage h) = some (layout 0 (lens h.pairs)).toArray := by
    rw [appMessage_eq]; exact fields_writeItems (lens_ok hok)
  have hvs : (layout 0 (lens h.pairs)).mapM
      (fun f => do pure (f.num, ← Serve.fieldValue (appMessage h) f)) = some h.pairs :=
    mapM_fieldValue h.pairs 0 hok (by rw [appMessage_eq]; exact At.self _)
  unfold appHeader
  rw [hfs]
  simp only [Option.bind_eq_bind, Option.bind_some] at hvs ⊢
  rw [hvs]
  obtain ⟨a, p, c, b, d, q⟩ := h
  cases d <;> cases q <;>
    simp [AppHeader.pairs, AppHeader.restPairs, fieldAudience, fieldApp, fieldChannel, fieldBody,
      fieldDescriptor, fieldPointers, hw, beq_self, guard]

/-- **An app message is canonical.** Bytes that read as an app message are exactly the bytes
`appMessage` writes for it, and it is well-formed: the meaning of an app record is unique. -/
theorem appMessage_appHeader {m : ByteArray} {h : AppHeader} (hm : appHeader m = some h) :
    appMessage h = m ∧ h.wellFormed = true := by
  have key : ∀ (h' : AppHeader),
      ((guard ((h'.wellFormed && appMessage h' == m) = true) : Option Unit).bind
        fun _ => some h') = some h → appMessage h = m ∧ h.wellFormed = true := by
    intro h' hb
    simp only [Option.bind_eq_some_iff, Option.some.injEq] at hb
    obtain ⟨u, hg, rfl⟩ := hb
    have := Encode.guard_eq_some hg
    simp only [Bool.and_eq_true] at this
    exact ⟨eq_of_beq this.2, this.1⟩
  unfold appHeader at hm
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def] at hm
  obtain ⟨fs, -, vs, -, hm⟩ := hm
  split at hm <;> (try simp only [Option.bind_some] at hm)
  all_goals first
    | exact key _ hm
    | simp at hm

theorem fst_of_mem_map_toList {d : Option ByteArray} {k : Nat} {p : Nat × ByteArray}
    (h : p ∈ (d.map (k, ·)).toList) : p.1 = k := by
  cases d with
  | none => simp at h
  | some v => simp only [Option.map_some, Option.toList_some, List.mem_singleton] at h; subst h; rfl

/-- The numbers of an app message's fields after 201. -/
theorem num_restPairs (h : AppHeader) : ∀ p ∈ h.restPairs, p.1 ∈ [210, 211, 212, 215, 216] := by
  intro p hp
  simp only [AppHeader.restPairs, List.mem_append, List.mem_cons, List.mem_nil_iff,
    or_false] at hp
  rcases hp with ((rfl | rfl | rfl) | hp) | hp
  · simp [fieldApp]
  · simp [fieldChannel]
  · simp [fieldBody]
  · simp [fst_of_mem_map_toList hp, fieldDescriptor]
  · simp [fst_of_mem_map_toList hp, fieldPointers]

/-- The numbers of an app message's fields. -/
theorem num_pairs (h : AppHeader) :
    ∀ it ∈ lens h.pairs, it.num ∈ [201, 210, 211, 212, 215, 216] := by
  intro it hit
  simp only [lens, List.mem_map] at hit
  obtain ⟨p, hp, rfl⟩ := hit
  simp only [AppHeader.pairs, List.mem_cons] at hp
  rcases hp with rfl | hp
  · simp [Item.num, fieldAudience]
  · have := num_restPairs h p hp
    simp only [Item.num]
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at this ⊢
    omega

/-- **`COMMIT` keeps an app message whole**: it holds no field 15 or 200, so its committed bytes
are itself. -/
theorem committedBytes_appMessage {h : AppHeader} (hw : h.wellFormed = true) :
    committedBytes (appMessage h) = some (appMessage h) := by
  rw [appMessage_eq]
  refine committedBytes_writeItems (lens_ok (pairs_ok hw)) fun it hit => ?_
  have := num_pairs h it hit
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at this
  omega

/-- An opening that reads as an app message is a nonce and that message, well-formed. -/
theorem appOf_spec {o : ByteArray} {h : AppHeader} (ho : appOf o = some h) :
    ∃ n : Nonce, o = n.bytes ++ appMessage h ∧ h.wellFormed = true := by
  unfold appOf at ho
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at ho
  obtain ⟨⟨n, m⟩, hs, hm⟩ := ho
  obtain ⟨he, hw⟩ := appMessage_appHeader hm
  exact ⟨n, by rw [splitOpening_eq hs, he], hw⟩

/-- **An app record's audience is its field 201.** The audience `ACCEPT` records and `SERVE`
checks for an app opening is the app message's audience, and there is one. -/
theorem appOf_audience {o : ByteArray} {h : AppHeader} (ho : appOf o = some h) :
    Serve.audienceOf o = Serve.parseAudience h.audience ∧ (Serve.audienceOf o).isSome := by
  obtain ⟨n, rfl, hw⟩ := appOf_spec ho
  have hok := lens_ok (pairs_ok hw)
  have ha : Serve.audienceOf (n.bytes ++ appMessage h) = Serve.parseAudience h.audience := by
    rw [appMessage_eq]
    refine audienceOf_items hok fun it hit => ?_
    simp only [List.mem_map] at hit
    obtain ⟨p, hp, rfl⟩ := hit
    have := num_restPairs h p hp
    simp only [Item.num]
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at this
    omega
  refine ⟨ha, ?_⟩
  rw [ha]
  simp only [AppHeader.wellFormed, Bool.and_eq_true] at hw
  exact hw.1.1.1.1.1.1.1

/-- **Tag separation from chat records.** An opening that reads as an app message is not
ephemeral (no field 5 or 14), and its committed bytes hold only the fields 201, 210, 211, 212,
215 and 216: no field 1 (a body), so no chat shows it as a message. -/
theorem app_not_chat {o : ByteArray} {h : AppHeader} (ho : appOf o = some h) :
    Serve.ephemeral o = false ∧ ∀ n m fs, splitOpening o = some (n, m) → fields m = some fs →
      ∀ f ∈ fs, f.num ∈ [201, 210, 211, 212, 215, 216] := by
  obtain ⟨n, rfl, hw⟩ := appOf_spec ho
  have hfs : fields (appMessage h) = some (layout 0 (lens h.pairs)).toArray := by
    rw [appMessage_eq]; exact fields_writeItems (lens_ok (pairs_ok hw))
  have hnum : ∀ f ∈ (layout 0 (lens h.pairs)).toArray,
      f.num ∈ [201, 210, 211, 212, 215, 216] := by
    intro f hf
    obtain ⟨it, hit, he⟩ := num_mem_layout (List.mem_toArray.1 hf)
    rw [← he]; exact num_pairs h it hit
  refine ⟨?_, fun n' m fs hs hf f hmem => ?_⟩
  · unfold Serve.ephemeral
    rw [splitOpening_append]
    simp only [hfs]
    rw [Array.any_eq_false]
    intro i hi
    have := hnum _ (Array.getElem_mem hi)
    simp only [List.mem_cons, List.mem_nil_iff, or_false, List.getElem_toArray] at this ⊢
    rcases this with h1 | h1 | h1 | h1 | h1 | h1 <;> simp [h1]
  · rw [splitOpening_append, Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨-, rfl⟩ := hs
    rw [hfs, Option.some.injEq] at hf
    subst hf
    exact hnum f hmem

/-- An app message's bytes: field 201, then field 210's key, then the rest. -/
theorem appMessage_split (h : AppHeader) :
    appMessage h = lenField 201 h.audience ++ (varint (210 * 8 + 2) ++
      (varint h.app.size ++ h.app ++ writeItems (lens (h.restPairs.drop 1)))) := by
  rw [appMessage_eq]
  simp [AppHeader.pairs, AppHeader.restPairs, lens, writeItems, Item.write, lenField,
    fieldAudience, fieldApp, ByteArray.append_assoc]

/-- **A piece is not an app record.** Its opening holds field 220 where an app message holds
field 210. -/
theorem appOf_pieceOpening (c : PieceCtx) (i : Nat) (b : ByteArray) :
    appOf (pieceOpening c i b) = none := by
  cases hA : appOf (pieceOpening c i b) with
  | none => rfl
  | some h =>
    exfalso
    obtain ⟨n, hn, hw⟩ := appOf_spec hA
    unfold pieceOpening at hn
    have hm := ((ByteArray.append_eq_append_iff_of_size_eq_left
      (by rw [Nonce.size_eq, Nonce.size_eq])).1 hn).2
    rw [appMessage_split] at hm
    have hx : h.audience.size < 2 ^ 70 :=
      (pairs_ok hw (fieldAudience, h.audience) (by simp [AppHeader.pairs])).2.2
    simp only [pieceMessage, varintField, fieldAudience, fieldPieceIndex,
      ByteArray.append_assoc] at hm
    obtain ⟨-, hr⟩ := lenField_cancel hm.symm hx
    have := congrArg (·[0]?) hr
    simp only [getElem?_zero_varint] at this
    revert this
    decide

/-- **A manifest is not an app record.** Its opening holds field 225 where an app message holds
field 210. -/
theorem appOf_manifestOpening (c : PieceCtx) : appOf (manifestOpening c) = none := by
  cases hA : appOf (manifestOpening c) with
  | none => rfl
  | some h =>
    exfalso
    obtain ⟨n, hn, hw⟩ := appOf_spec hA
    unfold manifestOpening at hn
    have hm := ((ByteArray.append_eq_append_iff_of_size_eq_left
      (by rw [Nonce.size_eq, Nonce.size_eq])).1 hn).2
    rw [appMessage_split] at hm
    have hx : h.audience.size < 2 ^ 70 :=
      (pairs_ok hw (fieldAudience, h.audience) (by simp [AppHeader.pairs])).2.2
    simp only [manifestMessage, fieldAudience, fieldOrdered, ByteArray.append_assoc] at hm
    obtain ⟨-, hr⟩ := lenField_cancel hm.symm hx
    have := congrArg (·[0]?) hr
    simp only [lenField, ByteArray.append_assoc, getElem?_zero_varint] at this
    revert this
    decide

/-! ### One record, one opening, one meaning -/

/-- **One commit, one opening.** Two openings that both match one commit (by one author in one
group) are equal, or SHA-256 has a collision. -/
theorem opening_bound {g : GroupId} {a : Aci} {c : Digest} {o₁ o₂ : ByteArray}
    (h₁ : openingMatches g a c o₁ = true) (h₂ : openingMatches g a c o₂ = true) :
    o₁ = o₂ ∨ Sha256Collision := by
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
  · exact .inl ((ByteArray.append_right_inj P).1 hx)
  · exact .inr ⟨_, _, hx, hc₁.trans hc₂.symm⟩

/-- **One record, one app meaning.** Two openings of one record read as the same app message (or
both as none), or SHA-256 has a collision. -/
theorem app_bound {g : GroupId} {a : Aci} {c : Digest} {o₁ o₂ : ByteArray}
    (h₁ : openingMatches g a c o₁ = true) (h₂ : openingMatches g a c o₂ = true) :
    appOf o₁ = appOf o₂ ∨ Sha256Collision :=
  (opening_bound h₁ h₂).imp (congrArg appOf) id

/-! ### Ids -/

/-- Equal ids from `hashToGroup` come from equal bytes, or SHA-256 has a collision. -/
theorem hashToGroup_eq {x y : ByteArray} (h : hashToGroup x = hashToGroup y) :
    x = y ∨ Sha256Collision := by
  by_cases hxy : x = y
  · exact .inl hxy
  · exact .inr ⟨x, y, hxy, Digest.ext_bytes (congrArg GroupId.bytes h)⟩

/-- A one-byte length below 256 is the length. -/
theorem u8_size_inj {p q : ByteArray} (hp : p.size < 256) (hq : q.size < 256)
    (h : Proto.Write.u8 p.size.toUInt8 = Proto.Write.u8 q.size.toUInt8) : p.size = q.size := by
  simp only [Proto.Write.u8, ByteArray.mk.injEq, Array.mk.injEq, List.cons.injEq,
    and_true] at h
  have := congrArg UInt8.toNat h
  simp at this
  omega

/-- **One channel id, one (Signal group, app, name).** Equal channel ids name the same Signal
group, app and channel, or SHA-256 has a collision. -/
theorem channelId_inj {g g' : GroupId} {p p' n n' : ByteArray}
    (hs : p.size < 256 ∧ p'.size < 256 ∧ n.size < 256 ∧ n'.size < 256)
    (h : channelId g p n = channelId g' p' n') :
    (g = g' ∧ p = p' ∧ n = n') ∨ Sha256Collision := by
  rcases hashToGroup_eq h with hx | hc
  · left
    simp only [ByteArray.append_assoc] at hx
    have h1 := (ByteArray.append_right_inj _).1 hx
    obtain ⟨hg, h2⟩ := (ByteArray.append_eq_append_iff_of_size_eq_left
      (by rw [g.size_eq, g'.size_eq])).1 h1
    obtain ⟨hu, h3⟩ := (ByteArray.append_eq_append_iff_of_size_eq_left (by rfl)).1 h2
    have hps := u8_size_inj hs.1 hs.2.1 hu
    obtain ⟨hp, h4⟩ := (ByteArray.append_eq_append_iff_of_size_eq_left hps).1 h3
    obtain ⟨-, hn⟩ := (ByteArray.append_eq_append_iff_of_size_eq_left (by rfl)).1 h4
    exact ⟨GroupId.ext_bytes hg, hp, hn⟩
  · exact .inr hc

/-- **A piece store is never a channel.** A piece-store id equal to a channel id is a SHA-256
collision (the domain tags `"zrdtT1"` and `"zrdtC1"` differ). -/
theorem storeId_ne_channelId {c g : GroupId} {a : Aci} {k : Nonce} {p n : ByteArray}
    (h : storeId c a k = channelId g p n) : Sha256Collision := by
  unfold storeId channelId at h
  rcases hashToGroup_eq h with hx | hc
  · exfalso
    have := congrArg (·[4]?) hx
    simp only [ByteArray.append_assoc] at this
    rw [getElem?_append, ite_eq_left (by decide), getElem?_append, ite_eq_left (by decide)] at this
    revert this
    decide
  · exact hc

/-! ### The descriptor reads back -/

theorem size_descriptorTag : descriptorTag.size = 6 := rfl

/-- The size of a descriptor's bytes. -/
theorem Descriptor.size_write (d : Descriptor) :
    d.write.size = 55 + 32 * d.ordered.size + d.manifest.size := by
  simp only [Descriptor.write, ByteArray.size_append, size_descriptorTag, d.nonce.size_eq, u64be,
    Encode.size_u32be, size_write_digests, size_write_bytes, size_u8]
  omega

/-- What a well-formed descriptor bounds: k is 20 or 10, 1 ≤ L ≤ 64 · 2^k, at most 64 digests,
a manifest of at most 4 KiB. -/
theorem Descriptor.bounds {d : Descriptor} (hw : d.wellFormed = true) :
    (d.exp = 20 ∨ d.exp = 10) ∧ 1 ≤ d.len ∧ d.len ≤ 64 * 2 ^ d.exp ∧ d.ordered.size ≤ 64 ∧
      d.manifest.size ≤ 4096 := by
  simp only [Descriptor.wellFormed, Bool.and_eq_true, decide_eq_true_eq, pieceExpOk,
    Bool.or_eq_true, beq_iff_eq, maxPieces, maxManifest, pieceExp, testPieceExp] at hw
  obtain ⟨⟨⟨⟨⟨hk, h1⟩, hL⟩, hN⟩, -⟩, hM⟩ := hw
  have hL := of_decide_eq_true hL
  have hM := of_decide_eq_true hM
  refine ⟨hk, h1, hL, ?_, hM⟩
  rw [hN]; unfold pieceCount
  have h1 : 2 ^ d.exp ≥ 1 := Nat.one_le_two_pow
  have : (d.len + 2 ^ d.exp - 1) / 2 ^ d.exp < 65 := by
    rw [Nat.div_lt_iff_lt_mul (by omega)]; omega
  omega

/-- **A well-formed descriptor reads back.** -/
theorem Descriptor.parse_write (d : Descriptor) (hw : d.wellFormed = true) :
    Descriptor.parse d.write = some d := by
  obtain ⟨hk, -, hL, hN, hM⟩ := Descriptor.bounds hw
  have hexp : d.exp < 256 := by omega
  have hlen : d.len < 2 ^ 64 := by
    have : 2 ^ d.exp ≤ 2 ^ 20 := Nat.pow_le_pow_right (by omega) (by omega)
    have : d.len ≤ 64 * 2 ^ 20 := Nat.le_trans hL (Nat.mul_le_mul_left _ this)
    omega
  have hcnt : d.ordered.size < 2 ^ 32 := by omega
  have hman : d.manifest.size < 2 ^ 32 := by omega
  have hA : At d.write 0 (descriptorTag ++ d.nonce.bytes ++ u64be d.len ++
      Proto.Write.u8 d.exp.toUInt8 ++ Proto.Write.digests d.ordered ++
      Proto.Write.bytes d.manifest) := At.self _
  have hT := hA.left.left.left.left.left
  have hNo := hA.left.left.left.left.right
  have hHi := hA.left.left.left.right.left
  have hLo := hA.left.left.left.right.right
  have hK := hA.left.left.right
  have hD := hA.left.right
  have hB := hA.right
  simp only [ByteArray.size_append, size_descriptorTag, d.nonce.size_eq, u64be,
    Encode.size_u32be, size_u8, size_write_digests, Nat.zero_add] at hNo hHi hLo hK hD hB
  have hsz := Descriptor.size_write d
  have p1 : pgo (Proto.Parser.take 6) d.write 0 = some (descriptorTag, 6) := by
    have := pgo_take_at hT (by rw [hsz, size_descriptorTag]; omega)
    rwa [size_descriptorTag] at this
  have p2 : pgo Proto.Parser.nonce d.write 6 = some (d.nonce, 38) := pgo_nonce_at hNo
  have p3 : pgo Proto.Parser.u32 d.write 38 = some (d.len / 2 ^ 32, 42) :=
    pgo_u32_at hHi (by omega)
  have p4 : pgo Proto.Parser.u32 d.write 42 = some (d.len % 2 ^ 32, 46) := by
    rw [← Encode.u32be_mod] at hLo
    exact pgo_u32_at hLo (Nat.mod_lt _ (by decide))
  have p5 : pgo Proto.Parser.u8 d.write 46 = some (d.exp.toUInt8, 47) := pgo_u8_at hK
  have p6 : pgo Proto.Parser.digests d.write 47 = some (d.ordered, 51 + 32 * d.ordered.size) :=
    pgo_digests_at hD hcnt
  have p7 : pgo Proto.Parser.bytes d.write (51 + 32 * d.ordered.size) =
      some (d.manifest, 55 + 32 * d.ordered.size + d.manifest.size) := by
    have e : 6 + 32 + (4 + 4) + 1 + (4 + 32 * d.ordered.size) = 51 + 32 * d.ordered.size := by
      omega
    rw [e] at hB
    rw [pgo_bytes_at hB hman]; congr 2; omega
  unfold Descriptor.parse readU64
  rw [run_eq]
  simp only [pgo_bind, pgo_ite, pgo_failure, pgo_pure, p1, Option.bind_some]
  simp only [bne, beq_self, Bool.not_true, Bool.false_eq_true, ↓reduceIte, p2, Option.bind_some,
    p3, p4, p5, p6, p7, hsz]
  simp only [Option.some.injEq]
  have : d.exp.toUInt8.toNat = d.exp := by simp; omega
  rw [this, Nat.div_add_mod' d.len (2 ^ 32)]

/-- **A descriptor is canonical.** Bytes that read as a descriptor are exactly its bytes. -/
theorem Descriptor.write_parse {b : ByteArray} {d : Descriptor} (h : Descriptor.parse b = some d) :
    d.write = b := by
  unfold Descriptor.parse readU64 at h
  rw [run_eq] at h
  simp only [pgo_bind, pgo_ite, pgo_failure, pgo_pure] at h
  simp only [Option.bind_eq_some_iff] at h
  obtain ⟨⟨d', q⟩, ⟨⟨t, q1⟩, h1, hrest⟩, hfin⟩ := h
  split at hfin
  case isFalse => cases hfin
  rename_i hq
  simp only [Option.some.injEq] at hfin
  subst hfin
  split at hrest
  case isTrue => simp at hrest
  rename_i htag
  obtain ⟨⟨n, q2⟩, h2, hrest⟩ := Option.bind_eq_some_iff.1 hrest
  obtain ⟨⟨len, q4⟩, h34, hrest⟩ := Option.bind_eq_some_iff.1 hrest
  obtain ⟨⟨hi, q3⟩, h3, h4'⟩ := Option.bind_eq_some_iff.1 h34
  obtain ⟨⟨lo, q4'⟩, h4, he⟩ := Option.bind_eq_some_iff.1 h4'
  simp only [Option.some.injEq, Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  obtain ⟨⟨k, q5⟩, h5, hrest⟩ := Option.bind_eq_some_iff.1 hrest
  obtain ⟨⟨ds, q6⟩, h6, hrest⟩ := Option.bind_eq_some_iff.1 hrest
  obtain ⟨⟨m, q7⟩, h7, hrest⟩ := Option.bind_eq_some_iff.1 hrest
  simp only [Option.some.injEq, Prod.mk.injEq] at hrest
  obtain ⟨rfl, rfl⟩ := hrest
  simp only at hq
  subst hq
  obtain ⟨rfl, -, e1⟩ := pgo_take_inv h1
  obtain ⟨rfl, -, e2⟩ := pgo_nonce_inv h2
  obtain ⟨rfl, -, e3, hhi⟩ := pgo_u32_inv h3
  obtain ⟨rfl, -, e4, hlo⟩ := pgo_u32_inv h4
  obtain ⟨rfl, -, e5⟩ := pgo_u8_inv h5
  obtain ⟨l6, -, e6, -⟩ := pgo_digests_inv h6
  obtain ⟨l7, -, e7, -⟩ := pgo_bytes_inv h7
  have ht : t = descriptorTag := by
    simp only [bne, Bool.not_eq_true', Bool.not_eq_false] at htag
    exact eq_of_beq (by simpa using htag)
  subst ht
  have hu : u64be (hi * 2 ^ 32 + lo) = u32be hi ++ u32be lo := by
    unfold u64be
    rw [← Encode.u32be_mod (hi * 2 ^ 32 + lo)]
    congr 2
    · omega
    · omega
  have hk : Proto.Write.u8 k.toNat.toUInt8 = ⟨#[k]⟩ := by simp [Proto.Write.u8]
  simp only [Descriptor.write]
  rw [hu, hk, ← e1, ← e2, ← e3, ← e4, ← e5, ← e6, ← e7, ← ByteArray.append_assoc,
    extract_glue (by omega) (by omega), extract_glue (by omega) (by omega),
    extract_glue (by omega) (by omega), extract_glue (by omega) (by omega),
    extract_glue (by omega) (by omega), extract_glue (by omega) l7, ByteArray.extract_zero_size]

/-! ### Pieces and the manifest: their openings match, with A's audience -/

theorem pieceMessage_eq (aud : ByteArray) (i : Nat) (b : ByteArray) :
    pieceMessage aud i b = writeItems [.len 201 aud, .vint 220 i, .len 221 b] := by
  simp [pieceMessage, writeItems, Item.write, fieldAudience, fieldPieceIndex, fieldPieceBytes,
    ByteArray.append_assoc, ByteArray.append_empty]

theorem manifestMessage_eq (c : PieceCtx) :
    manifestMessage c = writeItems [.len 201 c.header.audience,
      .len 225 (linksBytes c.desc.ordered), .len 226 c.desc.manifest] := by
  simp [manifestMessage, writeItems, Item.write, fieldAudience, fieldOrdered, fieldManifest,
    ByteArray.append_assoc, ByteArray.append_empty]

/-- **A piece's opening matches its record, and carries A's audience** (BUILD_M1 §C.1; the
bounds `hi` and `hb` are the corrected statement's: a varint holds at most 2^70, so bytes of
2^70 or more would not read back; `pieceOk_opening` discharges them for every checked piece). -/
theorem pieceOpening_matches (c : PieceCtx) (i : Nat) (b : ByteArray) (hi : i < 2 ^ 32)
    (hb : b.size < 2 ^ 32) (ha : Serve.parseAudience c.header.audience = some c.seats) :
    openingMatches c.storeId c.author (pieceRecord c i b).commit (pieceOpening c i b) = true ∧
      Serve.audienceOf (pieceOpening c i b) = some c.seats := by
  have hasz := size_of_parseAudience ha
  simp only [Serve.maxAudience] at hasz
  have ho : ∀ it ∈ [Item.len 201 c.header.audience, .vint 220 i, .len 221 b], it.ok := by
    intro it hit
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hit
    rcases hit with rfl | rfl | rfl <;> simp only [Item.ok] <;> omega
  refine ⟨?_, ?_⟩
  · simp only [pieceRecord, Rec.commit_make, pieceOpening, pieceMessage_eq, commitOf]
    exact openingMatches_items ho fun it hit => by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hit
      rcases hit with rfl | rfl | rfl <;> simp [Item.num]
  · simp only [pieceOpening, pieceMessage_eq]
    rw [audienceOf_items ho (fun it hit => by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hit
      rcases hit with rfl | rfl <;> simp [Item.num]), ha]

/-- **The manifest's opening matches F, and carries A's audience** (the corrected statement
assumes a well-formed descriptor, as every bound context has: it bounds the field sizes). -/
theorem manifestOpening_matches (c : PieceCtx) (hw : c.desc.wellFormed = true)
    (ha : Serve.parseAudience c.header.audience = some c.seats) :
    openingMatches c.storeId c.author (manifestRecord c).commit (manifestOpening c) = true ∧
      Serve.audienceOf (manifestOpening c) = some c.seats := by
  have hasz := size_of_parseAudience ha
  simp only [Serve.maxAudience] at hasz
  obtain ⟨-, -, -, hN, hM⟩ := Descriptor.bounds hw
  have ho : ∀ it ∈ [Item.len 201 c.header.audience, .len 225 (linksBytes c.desc.ordered),
      .len 226 c.desc.manifest], it.ok := by
    intro it hit
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hit
    rcases hit with rfl | rfl | rfl <;> simp only [Item.ok, Encode.size_linksBytes] <;> omega
  refine ⟨?_, ?_⟩
  · simp only [manifestRecord, Rec.commit_make, manifestOpening, manifestMessage_eq, commitOf]
    exact openingMatches_items ho fun it hit => by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hit
      rcases hit with rfl | rfl | rfl <;> simp [Item.num]
  · simp only [manifestOpening, manifestMessage_eq]
    rw [audienceOf_items ho (fun it hit => by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hit
      rcases hit with rfl | rfl <;> simp [Item.num]), ha]

/-- `pieceOpening_matches` for a piece that passes `pieceOk` under a well-formed descriptor (every
context `bindCtx` gives, `bindCtx_spec`): its bounds hold. -/
theorem pieceOk_opening {c : PieceCtx} {i : Nat} {b : ByteArray} (hw : c.desc.wellFormed = true)
    (ha : Serve.parseAudience c.header.audience = some c.seats) (hp : pieceOk c i b = true) :
    openingMatches c.storeId c.author (pieceRecord c i b).commit (pieceOpening c i b) = true ∧
      Serve.audienceOf (pieceOpening c i b) = some c.seats := by
  obtain ⟨hk, -, -, hN, -⟩ := Descriptor.bounds hw
  unfold pieceOk at hp
  split at hp
  · cases hp
  · rename_i d hd
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    have hi : i < c.desc.ordered.size := by
      rcases Nat.lt_or_ge i c.desc.ordered.size with h | h
      · exact h
      · rw [Array.getElem?_eq_none h] at hd; cases hd
    have hb : b.size ≤ 2 ^ 20 := by
      rw [hp.1]; unfold pieceLen
      have : 2 ^ c.desc.exp ≤ 2 ^ 20 := Nat.pow_le_pow_right (by omega) (by omega)
      exact Nat.le_trans (Nat.min_le_left _ _) this
    exact pieceOpening_matches c i b (by omega) (by omega) ha

/-! ### Honest announcements bind -/

/-- **An app message's opening reads back as it.** -/
theorem appOf_append (n : Nonce) {h : AppHeader} (hw : h.wellFormed = true) :
    appOf (n.bytes ++ appMessage h) = some h := by
  unfold appOf
  rw [splitOpening_append]
  exact appHeader_appMessage hw

/-- **An app message's opening matches its commitment** (`COMMIT` of the message gives both). -/
theorem appOpening_matches (g : GroupId) (a : Aci) (n : Nonce) {h : AppHeader}
    (hw : h.wellFormed = true) :
    openingMatches g a (commitOf g a n (appMessage h)) (n.bytes ++ appMessage h) = true := by
  rw [commitOf, appMessage_eq]
  refine openingMatches_items (lens_ok (pairs_ok hw)) fun it hit => ?_
  have := num_pairs h it hit
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at this
  omega

theorem groupId_beq_self (g : GroupId) : (g == g) = true := beq_self_eq_true g

/-- **An honest announcement binds.** The record of an app message of `app` with a well-formed
descriptor, committed by `a` in the channel `channelId sg app name` of its own channel name, binds
with its opening, to the context of that message. -/
theorem bindCtx_complete {sg : GroupId} {h : AppHeader} {d : Descriptor} {a : Aci} {n : Nonce}
    {ls : Array Digest} (hw : h.wellFormed = true) (hd : h.descriptor = some d.write)
    (hdw : d.wellFormed = true) :
    ∃ seats, Serve.parseAudience h.audience = some seats ∧
      bindCtx sg h.app (Rec.make (channelId sg h.app h.channel)
          (commitOf (channelId sg h.app h.channel) a n (appMessage h)) ls a)
        (n.bytes ++ appMessage h) =
      .ok ⟨hashRecord (Rec.make (channelId sg h.app h.channel)
          (commitOf (channelId sg h.app h.channel) a n (appMessage h)) ls a),
        channelId sg h.app h.channel, a, h, seats, d⟩ := by
  have ha : (Serve.parseAudience h.audience).isSome = true := by
    simp only [AppHeader.wellFormed, Bool.and_eq_true] at hw
    exact hw.1.1.1.1.1.1.1
  obtain ⟨seats, hs⟩ := Option.isSome_iff_exists.mp ha
  refine ⟨seats, hs, ?_⟩
  unfold bindCtx
  simp only [pure, Except.pure, Rec.group_make, Rec.author_make, Rec.commit_make, appOpening_matches _ _ _ hw,
    appOf_append _ hw, beq_self, groupId_beq_self, Bool.and_self, hd,
    Descriptor.parse_write d hdw, hdw, hs, ↓reduceIte]

/-! ### Binding, and what the read-only base ops say -/

/-- **What a bound context is.** `bindCtx` succeeds only on an opening that matches A and reads
as an app message of the requested app whose channel id (from the Signal group, the app and the
committed channel name) is A's group, with a well-formed descriptor; the context holds A's digest,
group and author, that message, its parsed audience, and the descriptor, whose bytes are the
message's field 215. -/
theorem bindCtx_spec {sg : GroupId} {app : ByteArray} {A : Rec} {o : ByteArray} {c : PieceCtx}
    (h : bindCtx sg app A o = .ok c) :
    c.announcement = hashRecord A ∧ c.channel = A.group ∧ c.author = A.author ∧
      openingMatches A.group A.author A.commit o = true ∧ appOf o = some c.header ∧
      c.header.app = app ∧ channelId sg c.header.app c.header.channel = A.group ∧
      c.header.descriptor = some c.desc.write ∧ c.desc.wellFormed = true ∧
      Serve.parseAudience c.header.audience = some c.seats := by
  unfold bindCtx at h
  simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at h
  split at h
  case isFalse => cases h
  rename_i hm
  split at h
  case h_2 => cases h
  rename_i hdr hA
  split at h
  case isFalse => cases h
  rename_i happ
  split at h
  case h_2 => cases h
  rename_i db hdb
  split at h
  case h_2 => cases h
  rename_i d hd
  split at h
  case isFalse => cases h
  rename_i hwf
  split at h
  case h_2 => cases h
  rename_i seats hseats
  cases h
  simp only [Bool.and_eq_true] at happ
  exact ⟨rfl, rfl, rfl, hm, hA, eq_of_beq happ.1, LawfulBEq.eq_of_beq happ.2,
    by rw [hdb, Descriptor.write_parse hd], hwf, hseats⟩

theorem firstBad_none (c : PieceCtx) (st : ByteArray) :
    firstBad c st = none ↔ assembleOk c st = true := by
  unfold firstBad assembleOk
  by_cases hs : st.size = c.desc.len
  · simp only [hs, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, beq_self_eq_true,
      Bool.true_and, List.find?_eq_none, List.all_eq_true, Bool.not_eq_true']
    constructor
    · intro h i hi; simpa using h i hi
    · intro h i hi; simpa using h i hi
  · have : (st.size != c.desc.len) = true := by simpa using hs
    simp [this, hs]

theorem run_assemble {s s' : State} {key : String} {st : ByteArray} {r : Reply}
    (h : run s (.assemble key st) = (r, s')) :
    s' = s ∧ (r = .ok ↔ ∃ c, s.ctxs[key]? = some c ∧ assembleOk c st = true) := by
  simp only [run, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  refine ⟨rfl, ?_⟩
  unfold assembleReply
  split
  · rename_i c hc
    rw [hc]
    constructor
    · intro hr
      refine ⟨c, rfl, (firstBad_none c st).1 ?_⟩
      split at hr
      · assumption
      · cases hr
    · rintro ⟨c', hc', ha⟩
      cases hc'
      rw [(firstBad_none c st).2 ha]
  · rename_i hc
    rw [hc]
    simp

theorem run_pieceOpening {s s' : State} {key : String} {i : Nat} {b o : ByteArray}
    (h : run s (.pieceOpening key i b) = (.opening o, s')) :
    s' = s ∧ ∃ c, s.ctxs[key]? = some c ∧ pieceOk c i b = true ∧ o = pieceOpening c i b := by
  simp only [run, Prod.mk.injEq] at h
  obtain ⟨h, rfl⟩ := h
  refine ⟨rfl, ?_⟩
  unfold openingOf at h
  split at h
  · rename_i c hc
    split at h
    · rename_i hp
      cases h
      exact ⟨c, hc, hp, rfl⟩
    · cases h
  · cases h

theorem run_channel {s s' : State} {sg g : GroupId} {p n : String}
    (h : run s (.channel sg p n) = (.channel g, s')) :
    g = channelId sg p.toUTF8 n.toUTF8 ∧ s' = s := by
  simp only [run, Prod.mk.injEq] at h
  obtain ⟨h, rfl⟩ := h
  split at h
  · cases h; exact ⟨rfl, rfl⟩
  · cases h


end Proofs

end Zrdt.AppBase
