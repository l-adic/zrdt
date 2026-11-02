import Zrdt.AppBase

/-!
# Torrent (docs/apps/BUILD_M1.md §B.6, §C.2)

**Owner: lane torrent.** Ops `0x20`-`0x27`: `BT_BUILD` `0x20`, `BT_FILE` `0x21`; `0x22`-`0x27`
reserved. Both ops only read the daemon's state (`run` returns no new state): every piece store
is created and filled by lane base's ops (`PIECES_BIND`, `PIECE_ACCEPT`, `PIECES_COMPLETE`), the
author's own included.

A torrent is one file, shared in a Signal group's channel `bt/files`:

- **The announcement A** is an app record (`AppBase.appMessage`) with app `"bt"`, channel
  `"files"`, body `"zbt1"` (`bodyTag`), the descriptor of its piece store (field 215) and, if the
  host gives any, the piece pointers (field 216).
- **The app manifest** (the descriptor's last field, and field 226 of the manifest record F) is
  `"zbtF1"` ‖ name (`str`) ‖ `u64` L (`manifestOf`). The name is one path component that is safe
  to create on every desktop the fork runs on (`safeComponent`).

**`BT_BUILD`** (`btBuild`) is pure. From the channel, the author, the store nonce, the piece size,
the audience (`AUDIENCE`'s value), the file name, the pointers and the file's bytes, it computes
the digest of every piece under the context that any member's `PIECES_BIND` of A gives, and A's
committed bytes. The host never assembles an app message: it passes these bytes to `COMMIT` and
sends them as Content 205. Before it answers, `btBuild` reads its own output back the way
`PIECES_BIND` will (`appHeader`, `committedBytes`, `Descriptor.parse`), so an `OK` is always an
announcement that binds (`btBuild_binds`), and any bind of it accepts exactly this file
(`btBuild_complete`).

**`BT_FILE`** (`fileOf`) reads the file name and length of a bound piece store from its context:
the manifest must be the canonical `manifestOf` of a safe name and of the descriptor's L.

The theorems about this module are in `core/Zrdt/PieceProofs.lean` (namespace `Zrdt.Torrent`,
so that the build text of `VERSION` covers the code only) and `Crdt/Merkle/AppsTorrent.lean`;
their statements are BUILD_M1 §C.2. The byte layouts are in the header of `core/Zrdt/Proto.lean`,
section `[lane torrent]`.
-/

namespace Zrdt.Torrent

open AppBase

/-! ## Constants -/

/-- The torrent app's body (field 212): exactly `"zbt1"`. -/
def bodyTag : ByteArray := "zbt1".toUTF8

/-- The tag that starts the app manifest: `"zbtF1"`. -/
def manifestTag : ByteArray := "zbtF1".toUTF8

/-- A file name is 1 to 255 bytes of UTF-8. -/
def maxName : Nat := 255

/-- `BT_BUILD`. -/
def opBuild : UInt8 := 0x20

/-- `BT_FILE`. -/
def opFile : UInt8 := 0x21

/-! ## File names (BUILD_M1 §B.6) -/

/-- The bytes no file name may hold, besides those below `0x20` and DEL: `/ \ : < > " | ? *`. -/
def forbiddenBytes : List UInt8 := [0x2F, 0x5C, 0x3A, 0x3C, 0x3E, 0x22, 0x7C, 0x3F, 0x2A]

/-- A byte no file name may hold: a control byte (NUL included), DEL, or a forbidden byte. -/
def badByte (x : UInt8) : Bool := x < 0x20 || x == 0x7F || forbiddenBytes.contains x

/-- Windows' reserved device names. -/
def reservedNames : List String :=
  ["CON", "PRN", "AUX", "NUL"] ++ (List.range 9).map (fun i => s!"COM{i + 1}") ++
    (List.range 9).map (fun i => s!"LPT{i + 1}")

/-- An ASCII letter in upper case; every other byte unchanged. -/
def upperAscii (x : UInt8) : UInt8 := if 0x61 ≤ x && x ≤ 0x7A then x - 0x20 else x

/-- The part of a name that Windows compares with the reserved names: the bytes before the first
dot, trailing spaces dropped. -/
def stem (b : List UInt8) : List UInt8 :=
  ((b.takeWhile (· != 0x2E)).reverse.dropWhile (· == 0x20)).reverse

/-- A reserved name of Windows, in any case, with or without an extension (`con`, `Com1.txt`,
`NUL .tar`). -/
def reservedName (b : List UInt8) : Bool :=
  reservedNames.any fun r => (stem b).map upperAscii == r.toUTF8.data.toList

/-- One path component that is safe to create on Linux, macOS and Windows: 1 to 255 bytes of
UTF-8; not `.` or `..`; no `/ \ : < > " | ? *`, NUL, byte below `0x20` or DEL; no leading or
trailing space or dot; not a reserved name of Windows (BUILD_M1 §B.6). -/
def safeComponent (name : String) : Bool :=
  let b := name.toUTF8.data.toList
  1 ≤ b.length && b.length ≤ maxName && name != "." && name != ".." && b.all (!badByte ·) &&
    b.head? != some 0x20 && b.head? != some 0x2E && b.getLast? != some 0x20 &&
    b.getLast? != some 0x2E && !reservedName b

#guard ["trip.mp4", "a", "notes v2.txt", "CONSOLE.txt", "com10", "lpt", "été.jpg"].all
  safeComponent
#guard !["", ".", "..", "a/b", "a\\b", "a:b", "a*", "x?", "<", "\"q\"", "a|b", "tab\tname",
  "del\x7F", "nul\x00", " lead", "trail ", ".hidden", "dot.", "CON", "con", "Com1.txt",
  "lpt9.tar.gz", "NUL .x", "aux"].any safeComponent
#guard safeComponent (String.ofList (List.replicate 255 'a')) &&
  !safeComponent (String.ofList (List.replicate 256 'a'))

/-! ## The app manifest -/

/-- The app manifest of a file: `"zbtF1"` ‖ name (`str`) ‖ `u64` L. -/
def manifestOf (name : String) (len : Nat) : ByteArray :=
  manifestTag ++ Proto.Write.str name ++ u64be len

/-- Read an app manifest; every byte must be used. -/
def parseManifest (m : ByteArray) : Option (String × Nat) :=
  Proto.Parser.run (do
    let t ← Proto.Parser.take 5
    if t != manifestTag then failure
    let name ← Proto.Parser.str
    let len ← readU64
    pure (name, len)) m 0

#guard parseManifest (manifestOf "trip.mp4" 20971520) == some ("trip.mp4", 20971520)
#guard parseManifest (manifestOf "trip.mp4" 3 ++ ⟨#[0]⟩) == none
#guard parseManifest ("zbtF2".toUTF8 ++ Proto.Write.str "a" ++ u64be 1) == none

/-! ## Requests and replies -/

/-- A torrent request. -/
inductive Request
  /-- `BT_BUILD`: channel ‖ author ‖ store nonce ‖ `u8` k ‖ audience (`bytes`) ‖ name (`str`) ‖
  pointers (`bytes`) ‖ stream (`bytes`). -/
  | build (channel : GroupId) (author : Aci) (nonce : Nonce) (exp : UInt8) (audience : ByteArray)
      (name : String) (pointers stream : ByteArray)
  /-- `BT_FILE`: piece key (`str`). -/
  | file (key : String)

/-- A torrent reply. -/
inductive Reply
  /-- `BT_BUILD`'s `OK`: A's committed bytes (`bytes`) ‖ the piece digests in index order
  (`ordered`). -/
  | built (message : ByteArray) (ordered : Array Digest)
  /-- `BT_FILE`'s `OK`: the name (`str`) ‖ `u64` L. -/
  | file (name : String) (len : Nat)
  /-- `BAD_NAME`: the name is not `safeComponent`. -/
  | badName
  /-- `BAD_APP` with its reason byte: 6 (`BT_BUILD`'s limits), 5 (`BT_FILE`: the manifest is not
  `manifestOf` of the descriptor's L), 7 (`BT_FILE`: the piece store is another app's). -/
  | badApp (why : BadApp)
  /-- `NO_CHAT`: no piece store under the key. -/
  | noChat

/-- The request's payload (op byte first). -/
def Request.write : Request → ByteArray
  | .build ch a n k aud name ptrs s =>
    Proto.Write.u8 opBuild ++ ch.bytes ++ a.bytes ++ n.bytes ++ Proto.Write.u8 k ++
      Proto.Write.bytes aud ++ Proto.Write.str name ++ Proto.Write.bytes ptrs ++ Proto.Write.bytes s
  | .file key => Proto.Write.u8 opFile ++ Proto.Write.str key

/-- The reply's payload (status byte first). -/
def Reply.write : Reply → ByteArray
  | .built m ord => Proto.Code.ok.write ++ Proto.Write.bytes m ++ Proto.Write.digests ord
  | .file name len => Proto.Code.ok.write ++ Proto.Write.str name ++ u64be len
  | .badName => Proto.Code.badName.write
  | .badApp why => Proto.Code.badApp.write ++ Proto.Write.u8 why.byte
  | .noChat => Proto.Code.noChat.write

/-- The body parser of torrent op `op` (`0x20`-`0x27`); `none`: not a torrent op. -/
def parse (op : UInt8) : Option (Proto.Parser Request) :=
  if op = opBuild then
    some (.build <$> Proto.Parser.group <*> Proto.Parser.aci <*> Proto.Parser.nonce <*>
      Proto.Parser.u8 <*> Proto.Parser.bytes <*> Proto.Parser.str <*> Proto.Parser.bytes <*>
      Proto.Parser.bytes)
  else if op = opFile then some (.file <$> Proto.Parser.str)
  else none

/-! ## `BT_BUILD` -/

/-- A torrent announcement's app message: app `"bt"`, channel `"files"`, body `"zbt1"`, the
descriptor's bytes, and the pointers if there are any. -/
def header (aud ptrs : ByteArray) (desc : Option ByteArray) : AppHeader :=
  { audience := aud, app := appTorrent, channel := channelTorrent, body := bodyTag,
    descriptor := desc, pointers := if ptrs.isEmpty then none else some ptrs }

/-- The context `BT_BUILD` hashes the slices under. A piece record reads only a context's channel,
author, store nonce and audience (`pieceRecord`), which are the ones every bind of the
announcement gives. -/
def buildCtx (ch : GroupId) (a : Aci) (nc : Nonce) (e : Nat) (aud : ByteArray)
    (seats : Array Serve.Seat) (len : Nat) (man : ByteArray) : PieceCtx :=
  { announcement := Digest.zero, channel := ch, author := a, header := header aud .empty none,
    seats := seats, desc := ⟨nc, len, e, #[], man⟩ }

/-- The digest of each slice of `s`, in index order, as piece records of context `c`. -/
def sliceDigests (c : PieceCtx) (s : ByteArray) : Array Digest :=
  (Array.range (pieceCount c.desc.exp s.size)).map fun i =>
    hashRecord (pieceRecord c i (slice c.desc.exp s i))

/-- The descriptor's bytes parse back to the descriptor. Lane base's `Descriptor.parse_write`
says they always do for a well-formed descriptor; `btBuild` checks it anyway, since
`PIECES_BIND` reads them. -/
def readsBack (d : Descriptor) : Bool :=
  match Descriptor.parse d.write with
  | some d' => d'.nonce.bytes == d.nonce.bytes && d'.len == d.len && d'.exp == d.exp &&
    d'.ordered == d.ordered && d'.manifest == d.manifest
  | none => false

/-- **`BT_BUILD`**: A's committed bytes, and its piece digests in index order, for the file `s`
named `name`, shared by `a` in channel `ch` with store nonce `nc`, pieces of 2^`e` bytes,
audience `aud` and pointers `ptrs`. It refuses a name that is not `safeComponent` (`BAD_NAME`) and
any input over the limits of BUILD_M1 §B.3 (`BAD_APP` 6). Pure: it reads no state. -/
def btBuild (ch : GroupId) (a : Aci) (nc : Nonce) (e : Nat) (aud : ByteArray) (name : String)
    (ptrs s : ByteArray) : Except Reply (ByteArray × Array Digest) := do
  unless safeComponent name do throw .badName
  unless pieceExpOk e && 1 ≤ s.size && s.size ≤ maxPieces * 2 ^ e && ptrs.size ≤ maxPointers do
    throw (.badApp .limits)
  let some seats := Serve.parseAudience aud | throw (.badApp .limits)
  let man := manifestOf name s.size
  let ord := sliceDigests (buildCtx ch a nc e aud seats s.size man) s
  let d : Descriptor := ⟨nc, s.size, e, ord, man⟩
  let h := header aud ptrs (some d.write)
  let msg := appMessage h
  -- Read it back as `PIECES_BIND` will: the limits, the app message, the committed bytes, the
  -- descriptor.
  unless d.wellFormed && h.wellFormed && appHeader msg == some h &&
      committedBytes msg == some msg && readsBack d do
    throw (.badApp .limits)
  pure (msg, ord)

/-! ## `BT_FILE` -/

/-- **`BT_FILE`** on a piece store's context: the file's name and length, read from the app
manifest. `BAD_APP` 7 if the store is another app's; `BAD_APP` 5 if the manifest does not parse,
or is not exactly `manifestOf` of its name and of the descriptor's L; `BAD_NAME` if the name is
not `safeComponent`. -/
def fileOf (c : PieceCtx) : Reply :=
  if c.header.app != appTorrent then .badApp .wrongApp
  else
    match parseManifest c.desc.manifest with
    | none => .badApp .descriptor
    | some (name, len) =>
      if len != c.desc.len || manifestOf name len != c.desc.manifest then .badApp .descriptor
      else if !safeComponent name then .badName
      else .file name len

/-! ## Running -/

/-- Answer a torrent request. Read-only: the state does not change. -/
def run (s : State) : Request → Reply
  | .build ch a n k aud name ptrs st =>
    match btBuild ch a n k.toNat aud name ptrs st with
    | .ok (m, ord) => .built m ord
    | .error r => r
  | .file key =>
    match s.ctxs[key]? with
    | none => .noChat
    | some c => fileOf c

/-! ## Examples -/

namespace TorrentExamples
open Zrdt.Examples AppExamples

/-- A 2.5 KiB file in pieces of 1 KiB (k = 10): three pieces, the last one 512 bytes. -/
def built : Except Reply (ByteArray × Array Digest) :=
  btBuild (channelId group appTorrent channelTorrent) alice Zrdt.Examples.nonce testPieceExp aud
    "trip.mp4" .empty stream

end TorrentExamples

open TorrentExamples in
#guard match built with
  | .ok (m, ord) => ord.size == 3 && (appHeader m).any (·.body == bodyTag) &&
    ((((appHeader m).bind (·.descriptor)).bind Descriptor.parse).any (·.ordered == ord))
  | .error _ => false
open AppExamples Zrdt.Examples in
#guard match btBuild group alice Zrdt.Examples.nonce testPieceExp aud "a/b" .empty stream with
  | .error .badName => true | _ => false
open AppExamples Zrdt.Examples in
-- k = 12 is not a piece size M1 accepts; an empty file; an audience that does not parse.
#guard [btBuild group alice Zrdt.Examples.nonce 12 aud "x" .empty stream,
    btBuild group alice Zrdt.Examples.nonce testPieceExp aud "x" .empty .empty,
    btBuild group alice Zrdt.Examples.nonce testPieceExp ⟨#[1]⟩ "x" .empty stream].all fun r =>
  match r with | .error (.badApp .limits) => true | _ => false

end Zrdt.Torrent
