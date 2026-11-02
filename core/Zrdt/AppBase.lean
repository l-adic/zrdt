import Zrdt.Proto

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

/-! ## Protobuf writing -/

/-- The protobuf varint of `n` (every number written here is below 2^64). -/
def varint (n : Nat) : ByteArray := go n 10 .empty
where
  /-- Seven bits per byte, low bits first; at most `fuel` bytes. -/
  go (n : Nat) : Nat → ByteArray → ByteArray
    | 0, acc => acc
    | fuel + 1, acc =>
      if n < 128 then acc.push n.toUInt8 else go (n / 128) fuel (acc.push (n % 128 + 128).toUInt8)

#guard varint 0 == ⟨#[0]⟩ && varint 300 == ⟨#[0xAC, 0x02]⟩
-- The key of field 201, wire type 2 (as `Commit.Examples.zrdtField` writes field 200's).
#guard varint (201 * 8 + 2) == ⟨#[0xCA, 0x0C]⟩

/-- A length-delimited field (wire type 2). -/
def lenField (num : Nat) (v : ByteArray) : ByteArray := varint (num * 8 + 2) ++ varint v.size ++ v

/-- A varint field (wire type 0). -/
def varintField (num : Nat) (v : Nat) : ByteArray := varint (num * 8) ++ varint v

/-- A 64-bit big-endian number (`u64`, BUILD_M1 §B.1). -/
def u64be (n : Nat) : ByteArray := u32be (n / 2 ^ 32) ++ u32be n

#guard u64be (2 ^ 32 + 7) == ⟨#[0, 0, 0, 1, 0, 0, 0, 7]⟩

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
    h.pointers.all (·.size ≤ maxPointers)

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
`PIECES_COMPLETE` `0x1B`, `ASSEMBLE` `0x1C`; `0x1D`-`0x1F` reserved. The skeleton has no op yet:
`parse` answers `none`, so `Zrdt.Apps` replies `UNKNOWN_OP`. -/

/-- A base request. -/
inductive Request : Type

/-- A base reply. -/
inductive Reply : Type

/-- The request's payload (op byte first). -/
def Request.write : Request → ByteArray := nofun

/-- The reply's payload (status byte first). -/
def Reply.write : Reply → ByteArray := nofun

/-- The body parser of base op `op` (`0x17`-`0x1F`); `none`: not a base op. -/
def parse (_op : UInt8) : Option (Proto.Parser Request) := none

/-- Carry out a base request. The only protocol-5 code that changes `State`. -/
def run (_s : State) : Request → Reply × State := nofun

end Zrdt.AppBase
