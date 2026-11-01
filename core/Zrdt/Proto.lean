import Std.Data.HashMap
import Zrdt.Commit
import Zrdt.Provenance

/-!
# The `zrdtd` frame protocol (docs/PLAN.md §3.3)

`zrdtd` reads requests on stdin and writes one reply per request on stdout, in request order.
Diagnostics go to stderr. This file fixes the bytes of every request and reply. The vectors
(`Zrdt.Vectors`, written to `vectors/vectors.json`) pin them.

## Frames

Every frame, in both directions, is `length (u32) ‖ payload`, where `length` is the number of
payload bytes. A request payload is `op (u8) ‖ body`. A reply payload is `status (u8) ‖ body`.

## Field types

All numbers are unsigned and big-endian.

- `u8`, `u32`: 1 and 4 bytes.
- `digest`, `group`, `nonce`: 32 bytes. `aci`: 16 bytes.
- `bytes`: a `u32` length, then that many bytes. `str`: `bytes` holding UTF-8 text.
- `digests`: a `u32` count, then that many `digest`s.
- `parts`: `group` ‖ commit (`digest`) ‖ links (`digests`) ‖ author (`aci`).
- `input`: a `u8` form, then: form 0, a store blob as `bytes`; form 1, a `u32` count, then that
  many encoded records, each as `bytes`.
- `fact`: `digest` ‖ provenance (`u8`: 0 live, 1 relayed, 2 imported) ‖ the relayer's `aci`
  (provenance 1 only) ‖ disown (`digests`).
- `status`: `u8` (0 confirmed by author, 1 not confirmed by author, 2 held by, 3 unconfirmed) ‖
  the member's `aci` (2 only).
- `opening`: `bytes` holding a nonce (32 bytes), then a DataMessage with its top-level fields 15
  and 200 removed (`Zrdt.Commit`).

- `chat` is a `str`: the host's conversation id.
- `parts` is a record (docs/PLAN.md §3.4). In a request, its links may come in any order and may
  repeat; `zrdtd` sorts them and drops the repeats (`Rec.make`). In a reply they are sorted, so
  `"zrdt2" ‖ parts` is exactly the record's encoding.
- A store blob and an encoded record are the encodings of docs/PLAN.md §3.4 (`Zrdt.Encode`).
- A request body must hold exactly its fields: nothing missing, nothing left over.
- Every digest list in a reply is sorted in byte order and has no repeats.

## Status byte

| Byte | Name | Body |
|---|---|---|
| `0x00` | `OK` | depends on the op (below) |
| `0x01` | `MISSING` | `digests`: the links that are not stored |
| `0x02` | `COLLISION` | `digest` |
| `0x03` | `WRONG_CHAT` | empty |
| `0x04` | `TOO_LARGE` | empty |
| `0x05` | `MALFORMED` | empty |
| `0x06` | `UNVERIFIABLE` | unverifiable (`digests`) ‖ missing (`digests`) |
| `0x07` | `NOT_FOUND` | empty |
| `0x08` | `BAD_OPENING` | empty |
| `0x80` | `BAD_REQUEST` | empty |
| `0x81` | `UNKNOWN_OP` | empty |
| `0x82` | `NO_CHAT` | empty |
| `0x83` | `CHAT_OPEN` | empty |

A status below `0x80` is an answer about the data. From `0x80` up, the host sent a request that
`zrdtd` cannot carry out, and nothing changed:

- `BAD_REQUEST`: the body does not have the layout of its op (a field cut short, bytes left over,
  a chat key that is not UTF-8, an unknown form, provenance or flag byte), or the payload is
  empty;
- `UNKNOWN_OP`: the op byte is not in the table below;
- `NO_CHAT`: no store is open under this chat key;
- `CHAT_OPEN`: a store is already open under this chat key.

## Ops

Request bodies:

| Op | Name | Request body |
|---|---|---|
| `0x01` | `VERSION` | empty |
| `0x02` | `NEW` | `chat` ‖ `group` |
| `0x03` | `OPEN` | `chat` ‖ `group` ‖ `input` |
| `0x04` | `SALVAGE` | `chat` ‖ `group` ‖ `input` |
| `0x05` | `COMMIT` | `group` ‖ author (`aci`) ‖ `nonce` ‖ DataMessage (`bytes`) |
| `0x06` | `HASH` | `parts` |
| `0x07` | `ACCEPT` | `chat` ‖ `parts` |
| `0x08` | `HEADS` | `chat` |
| `0x09` | `HAS` | `chat` ‖ `digest` |
| `0x0A` | `GET` | `chat` ‖ `digest` |
| `0x0B` | `REACH_SET` | `chat` ‖ from (`digests`) |
| `0x0C` | `MERGE` | `chat` ‖ store blob (`bytes`) |
| `0x0D` | `CLASSIFY` | `chat` ‖ a `u32` count ‖ that many `fact`s |
| `0x0E` | `ENCODE` | `chat` |
| `0x0F` | `CLOSE` | `chat` |
| `0x10` | `ACCEPT_RECORD` | `chat` ‖ record (`bytes`) ‖ `u8` (1: an `opening` follows, 0: none) |

Replies (every op can also reply `BAD_REQUEST`):

- `VERSION`: `OK`: protocol (`u32`) ‖ build (`str`).
- `NEW`: `OK`; `CHAT_OPEN`.
- `OPEN`: `OK`; `MALFORMED`, `TOO_LARGE`, `WRONG_CHAT`, `COLLISION`, `UNVERIFIABLE`,
  `CHAT_OPEN`.
- `SALVAGE`: `OK`: dropped (`digests`) ‖ missing (`digests`); `MALFORMED`, `TOO_LARGE`,
  `WRONG_CHAT`, `COLLISION`, `CHAT_OPEN`.
- `COMMIT`: `OK`: the commitment (`digest`) ‖ the `opening`; `MALFORMED`.
- `HASH`: `OK`: the record's digest.
- `ACCEPT`: `OK` (accepted): the record's digest ‖ its encoding (`bytes`); `MISSING`,
  `COLLISION`, `WRONG_CHAT`, `TOO_LARGE`, `NO_CHAT`.
- `ACCEPT_RECORD`: as `ACCEPT`, and also `MALFORMED`, `BAD_OPENING`.
- `HEADS`: `OK`: `digests`; `NO_CHAT`.
- `HAS`: `OK`: `u8` (1 stored, 0 not); `NO_CHAT`.
- `GET`: `OK`: `parts`; `NOT_FOUND`, `NO_CHAT`.
- `REACH_SET`: `OK`: `digests`; `NO_CHAT`.
- `MERGE`: `OK`; `MALFORMED`, `TOO_LARGE`, `WRONG_CHAT`, `COLLISION`, `UNVERIFIABLE`,
  `NO_CHAT`.
- `CLASSIFY`: `OK`: a `u32` count ‖ that many (`digest` ‖ `status`), one per stored record,
  sorted by digest; `NO_CHAT`.
- `ENCODE`: `OK`: the store blob (`bytes`); `NO_CHAT`.
- `CLOSE`: `OK`.

## What the replies mean

- `ACCEPT` → `OK`: the record is stored, now or before (a byte-identical duplicate is accepted);
  the digest is the record's (`hashRecord`), and the bytes are its canonical encoding (links
  sorted, repeats dropped), the bytes to relay or store.
- `ACCEPT_RECORD`: accept a record that came as bytes (relayed or imported), optionally with its
  opening. The bytes must be exactly a record's encoding, otherwise `MALFORMED`. If an opening is
  given, its commitment under the record's group and author must be the record's commit, and it
  must hold no field 15 or 200 (`openingMatches`), otherwise `BAD_OPENING`. Both are checked
  before the store is touched, and then the record goes through `accept` as for `ACCEPT`. Order of
  checks: `NO_CHAT`, `MALFORMED`, `BAD_OPENING`, then `accept`'s.
- `MISSING`: the store is unchanged; the list holds exactly the links that are not stored, and
  is never empty.
- `COLLISION`: nothing changed; a different record with this digest is stored, or is in the
  input.
- `WRONG_CHAT`: nothing changed; the record, the blob, or a record in it belongs to another chat.
- `TOO_LARGE`: nothing changed; the limits of docs/PLAN.md §3.4 would be broken (a record with
  more than 4096 links, or a store of 2^24 records or more). A blob whose count field is 2^24 or
  more is `TOO_LARGE` before any record is read (`blobTooLarge`).
- `MALFORMED`: for `OPEN`, `SALVAGE` and `MERGE`, the bytes are not a store blob, or a listed
  record does not decode; for `COMMIT`, the DataMessage is not a well-formed protobuf message
  (`Zrdt.Commit`); for `ACCEPT_RECORD`, the bytes are not a record.
- `BAD_OPENING` (`ACCEPT_RECORD`): nothing changed; the opening does not belong to the record.
- `UNVERIFIABLE` (`OPEN`, `MERGE`): nothing changed; some records can never be accepted.
  `unverifiable` lists their digests, and `missing` the link digests that point to no record.
- `OPEN`, `SALVAGE`, `MERGE`: the records of a blob may come in any order, and a byte-identical
  repeat counts once.
- `SALVAGE` → `OK`: the records that can be accepted are loaded; `dropped` names the rest, and
  `missing` the link digests they lack.
- `COMMIT` → `OK`: the commitment, and the opening the app stores and relays in place of the
  message (`commitWithOpening`). `COMMIT` of the opening's bytes gives the same commitment.
- `CLASSIFY`: the status of every stored record (`Zrdt.Provenance`). Facts about digests that are
  not stored are ignored. A record held by several members names the one with the smallest ACI
  in byte order.
- `VERSION`: the protocol is 2. The build text names the package version and the first 16 hex
  digits of SHA-256 over the Lean sources of the modules `zrdtd` runs, `Zrdtd/Main.lean`
  included (`buildIdOf`).

## The table of open stores

`NEW`, `OPEN` and `SALVAGE` put a store under a chat key that is not in use (otherwise
`CHAT_OPEN`). After that, only `ACCEPT`, `ACCEPT_RECORD` and `MERGE` change the store, and `CLOSE`
removes it. So under one chat key a store only grows, until `CLOSE`. A failed `OPEN`, `SALVAGE`,
`MERGE` or `ACCEPT_RECORD` changes nothing. `CLOSE` on a chat key that is not in use replies `OK`.

`ACCEPT`, `ACCEPT_RECORD` and `MERGE` take the store out of the table before they change it, and
put the result back. For `ACCEPT` the table then holds no second reference to the store, so
`accept` updates it in place. `MERGE` keeps the original to put back if the merge fails; the
merged store shares most of its tree with it.
-/

namespace Zrdt.Proto

/-! ## Status bytes and op bytes -/

/-- The first byte of a reply (table in the module header). -/
inductive Code
  | ok | missing | collision | wrongChat | tooLarge | malformed | unverifiable | notFound
  | badOpening | badRequest | unknownOp | noChat | chatOpen
deriving DecidableEq, Repr

/-- The byte of each status. -/
def Code.byte : Code → UInt8
  | .ok => 0x00 | .missing => 0x01 | .collision => 0x02 | .wrongChat => 0x03
  | .tooLarge => 0x04 | .malformed => 0x05 | .unverifiable => 0x06 | .notFound => 0x07
  | .badOpening => 0x08
  | .badRequest => 0x80 | .unknownOp => 0x81 | .noChat => 0x82 | .chatOpen => 0x83

/-- The name of each status, as in the module header. -/
def Code.name : Code → String
  | .ok => "OK" | .missing => "MISSING" | .collision => "COLLISION"
  | .wrongChat => "WRONG_CHAT" | .tooLarge => "TOO_LARGE" | .malformed => "MALFORMED"
  | .unverifiable => "UNVERIFIABLE" | .notFound => "NOT_FOUND" | .badOpening => "BAD_OPENING"
  | .badRequest => "BAD_REQUEST"
  | .unknownOp => "UNKNOWN_OP" | .noChat => "NO_CHAT" | .chatOpen => "CHAT_OPEN"

/-- Every status. -/
def Code.all : List Code :=
  [.ok, .missing, .collision, .wrongChat, .tooLarge, .malformed, .unverifiable, .notFound,
    .badOpening, .badRequest, .unknownOp, .noChat, .chatOpen]

/-- The status with this byte, if any. -/
def Code.ofByte? (b : UInt8) : Option Code := Code.all.find? (·.byte == b)

#guard Code.ofByte? 0x83 == some .chatOpen
#guard Code.ofByte? 0x08 == some .badOpening
#guard Code.ofByte? 0x09 == none
-- Every status has its own byte.
#guard (Code.all.map Code.byte).eraseDups.length == Code.all.length

/-- The op names, in op-byte order: `0x01` is `VERSION`, `0x10` is `ACCEPT_RECORD`. -/
def opNames : Array String :=
  #["VERSION", "NEW", "OPEN", "SALVAGE", "COMMIT", "HASH", "ACCEPT", "HEADS", "HAS", "GET",
    "REACH_SET", "MERGE", "CLASSIFY", "ENCODE", "CLOSE", "ACCEPT_RECORD"]

/-- The name of the op with this byte, if any. -/
def opName? (b : UInt8) : Option String := if b = 0 then none else opNames[b.toNat - 1]?

#guard opName? 0x0B == some "REACH_SET"
#guard opName? 0x10 == some "ACCEPT_RECORD"
#guard opName? 0x00 == none && opName? 0x11 == none

/-- The protocol version. It changes when a request or reply layout changes. Version 2: the
`ACCEPT` and `COMMIT` replies carry the record bytes and the opening; `ACCEPT_RECORD` is new. -/
def protocolVersion : Nat := 2

/-! ## Writing fields -/

namespace Write

/-- One byte. -/
def u8 (x : UInt8) : ByteArray := ⟨#[x]⟩

/-- `bytes`: a 4-byte length, then the bytes. -/
def bytes (b : ByteArray) : ByteArray := u32be b.size ++ b

/-- `str`: the UTF-8 bytes of `s`, as `bytes`. -/
def str (s : String) : ByteArray := bytes s.toUTF8

/-- `digests`: a 4-byte count, then the digests. -/
def digests (ds : Array Digest) : ByteArray :=
  ds.foldl (fun acc d => acc ++ d.bytes) (u32be ds.size)

#guard str "hi" == ⟨#[0, 0, 0, 2, 0x68, 0x69]⟩
#guard (digests #[Digest.zero]).size == 36

end Write

/-! ## Reading fields -/

/-- Reads a request: from a position in the payload, a value and the next position, or `none`
if the bytes do not have the expected layout. -/
abbrev Parser := StateT Nat (ReaderT ByteArray Option)

namespace Parser

/-- Run `p` on `payload` from position `start`. It must use up every byte. -/
def run {α : Type} (p : Parser α) (payload : ByteArray) (start : Nat) : Option α :=
  let whole : Parser α := do
    let x ← p
    if (← get) = (← read).size then pure x else failure
  (whole.run' start).run payload

/-- The next `n` bytes. -/
def take (n : Nat) : Parser ByteArray := do
  let b ← read
  let p ← get
  if p + n ≤ b.size then
    set (p + n)
    pure (b.extract p (p + n))
  else failure

/-- One byte. -/
def u8 : Parser UInt8 := do
  let b ← read
  let p ← get
  if h : p < b.size then
    set (p + 1)
    pure b[p]
  else failure

/-- A 4-byte number. -/
def u32 : Parser Nat := do
  match readU32? (← read) (← get) with
  | some n => modify (· + 4); pure n
  | none => failure

/-- `bytes`. The length is checked against the input before anything is copied. -/
def bytes : Parser ByteArray := do take (← u32)

/-- `str`: `bytes` that must be UTF-8. -/
def str : Parser String := do
  match String.fromUTF8? (← bytes) with
  | some s => pure s
  | none => failure

/-- A `digest` (32 bytes). -/
def digest : Parser Digest := do
  match Digest.ofBytes? (← take 32) with
  | some d => pure d
  | none => failure

/-- A `group` (32 bytes). -/
def group : Parser GroupId := do
  match GroupId.ofBytes? (← take 32) with
  | some g => pure g
  | none => failure

/-- An `aci` (16 bytes). -/
def aci : Parser Aci := do
  match Aci.ofBytes? (← take 16) with
  | some a => pure a
  | none => failure

/-- A `nonce` (32 bytes). -/
def nonce : Parser Nonce := do
  match Nonce.ofBytes? (← take 32) with
  | some n => pure n
  | none => failure

/-- `digests`. A count the input cannot hold is rejected before any digest is read. -/
def digests : Parser (Array Digest) := do
  let n ← u32
  let b ← read
  let p ← get
  if p + 32 * n ≤ b.size then
    match readDigests b p #[] n with
    | some ds => set (p + 32 * n); pure ds
    | none => failure
  else failure

/-- `n` items read by `item`, each at least `minSize` bytes long. A count the rest of the input
cannot hold is rejected before any item is read. -/
def many {α : Type} (item : Parser α) (minSize : Nat) (n : Nat) : Parser (Array α) := do
  if n * minSize ≤ (← read).size - (← get) then go n #[] else failure
where
  /-- Read `k` more items after `acc`. -/
  go : Nat → Array α → Parser (Array α)
    | 0, acc => pure acc
    | k + 1, acc => do go k (acc.push (← item))

#guard (u32.run ⟨#[0, 0, 1, 0]⟩ 0) == some 256
#guard (u32.run ⟨#[0, 0, 1, 0, 9]⟩ 0) == none                    -- a byte left over
#guard (str.run ⟨#[0, 0, 0, 2, 0x68, 0x69]⟩ 0) == some "hi"
#guard (str.run ⟨#[0, 0, 0, 1, 0xff]⟩ 0) == none                 -- not UTF-8
#guard (digests.run (Write.digests #[Digest.zero]) 0) == some #[Digest.zero]
-- A count of 2^32 - 1 digests with no digests after it is rejected at once.
#guard (digests.run ⟨#[0xff, 0xff, 0xff, 0xff]⟩ 0) == none

end Parser

/-! ## Requests -/

/-- A record as the host sends it: its links may come in any order and may repeat. -/
structure Parts where
  /-- The chat. -/
  group : GroupId
  /-- The commitment to the message (`Zrdt.commit`). -/
  commit : Digest
  /-- The digests the record links. -/
  links : Array Digest
  /-- The sender's account id. -/
  author : Aci

/-- The record: links sorted, repeats dropped. -/
def Parts.toRec (p : Parts) : Rec := Rec.make p.group p.commit p.links p.author

/-- The parts of a record (its links are already sorted). -/
def Parts.ofRec (r : Rec) : Parts := ⟨r.group, r.commit, r.links, r.author⟩

open Examples in
#guard (Parts.toRec ⟨group, dig 0xc1, #[dig 3, dig 1, dig 3, dig 2], alice⟩) == reply

/-- The records given to `OPEN` or `SALVAGE`: a store blob, or a list of encoded records. -/
inductive Input
  | blob (b : ByteArray)
  | records (rs : Array ByteArray)

/-- A request (ops in the module header). -/
inductive Request
  | version
  | new (chat : String) (group : GroupId)
  | «open» (chat : String) (group : GroupId) (input : Input)
  | salvage (chat : String) (group : GroupId) (input : Input)
  | commit (group : GroupId) (author : Aci) (nonce : Nonce) (dataMessage : ByteArray)
  | hash (parts : Parts)
  | accept (chat : String) (parts : Parts)
  | heads (chat : String)
  | has (chat : String) (d : Digest)
  | get (chat : String) (d : Digest)
  | reachSet (chat : String) (start : Array Digest)
  | merge (chat : String) (blob : ByteArray)
  | classify (chat : String) (facts : Array Fact)
  | encode (chat : String)
  | close (chat : String)
  | acceptRecord (chat : String) (record : ByteArray) (opening : Option ByteArray)

/-- The op byte and name of each request. -/
def Request.op : Request → UInt8 × String
  | .version => (0x01, "VERSION") | .new .. => (0x02, "NEW") | .open .. => (0x03, "OPEN")
  | .salvage .. => (0x04, "SALVAGE") | .commit .. => (0x05, "COMMIT")
  | .hash .. => (0x06, "HASH") | .accept .. => (0x07, "ACCEPT") | .heads .. => (0x08, "HEADS")
  | .has .. => (0x09, "HAS") | .get .. => (0x0A, "GET") | .reachSet .. => (0x0B, "REACH_SET")
  | .merge .. => (0x0C, "MERGE") | .classify .. => (0x0D, "CLASSIFY")
  | .encode .. => (0x0E, "ENCODE") | .close .. => (0x0F, "CLOSE")
  | .acceptRecord .. => (0x10, "ACCEPT_RECORD")

namespace Write

/-- `parts`. -/
def parts (p : Parts) : ByteArray :=
  p.group.bytes ++ p.commit.bytes ++ digests p.links ++ p.author.bytes

/-- `input`. -/
def input : Input → ByteArray
  | .blob b => u8 0 ++ bytes b
  | .records rs => rs.foldl (fun acc r => acc ++ bytes r) (u8 1 ++ u32be rs.size)

/-- `fact`. -/
def fact (f : Fact) : ByteArray :=
  f.digest.bytes ++
    (match f.provenance with
      | .live => u8 0
      | .relayed a => u8 1 ++ a.bytes
      | .imported => u8 2) ++
    digests f.disown

/-- `status` (of a record, in a `CLASSIFY` reply). -/
def status : Status → ByteArray
  | .confirmedByAuthor => u8 0
  | .notConfirmedByAuthor => u8 1
  | .heldBy a => u8 2 ++ a.bytes
  | .unconfirmed => u8 3

open Examples in
-- In a reply, `"zrdt2" ‖ parts` is the record's encoding.
#guard recordTag ++ parts (Parts.ofRec reply) == Zrdt.encode reply

end Write

/-- The payload of a request: its op byte, then its body. -/
def Request.write (q : Request) : ByteArray :=
  Write.u8 q.op.1 ++
    match q with
    | .version => .empty
    | .new c g => Write.str c ++ g.bytes
    | .open c g i | .salvage c g i => Write.str c ++ g.bytes ++ Write.input i
    | .commit g a n m => g.bytes ++ a.bytes ++ n.bytes ++ Write.bytes m
    | .hash p => Write.parts p
    | .accept c p => Write.str c ++ Write.parts p
    | .heads c | .encode c | .close c => Write.str c
    | .has c d | .get c d => Write.str c ++ d.bytes
    | .reachSet c ds => Write.str c ++ Write.digests ds
    | .merge c b => Write.str c ++ Write.bytes b
    | .classify c fs => fs.foldl (fun acc f => acc ++ Write.fact f) (Write.str c ++ u32be fs.size)
    | .acceptRecord c r o =>
      Write.str c ++ Write.bytes r ++
        match o with
        | none => Write.u8 0
        | some o => Write.u8 1 ++ Write.bytes o

#guard (Request.close "x").write == ⟨#[0x0F, 0, 0, 0, 1, 0x78]⟩
-- `Request.op` and `opNames` agree.
#guard [Request.version, .heads "c", .close "c", .acceptRecord "c" .empty none].all fun q =>
  opName? q.op.1 == some q.op.2

namespace Parser

/-- `parts`. -/
def parts : Parser Parts := do
  let g ← group
  let c ← digest
  let ls ← digests
  let a ← aci
  pure ⟨g, c, ls, a⟩

/-- `input`. Each listed record takes at least its 4-byte length. -/
def input : Parser Input := do
  match ← u8 with
  | 0 => .blob <$> bytes
  | 1 => .records <$> many bytes 4 (← u32)
  | _ => failure

/-- `fact`. -/
def fact : Parser Fact := do
  let d ← digest
  let p ← match ← u8 with
    | 0 => pure Provenance.live
    | 1 => Provenance.relayed <$> aci
    | 2 => pure Provenance.imported
    | _ => failure
  let dis ← digests
  pure ⟨d, p, dis⟩

/-- The body of each op. `none` for an unknown op byte. -/
def body : UInt8 → Option (Parser Request)
  | 0x01 => some (pure .version)
  | 0x02 => some (.new <$> str <*> group)
  | 0x03 => some (.open <$> str <*> group <*> input)
  | 0x04 => some (.salvage <$> str <*> group <*> input)
  | 0x05 => some (.commit <$> group <*> aci <*> nonce <*> bytes)
  | 0x06 => some (.hash <$> parts)
  | 0x07 => some (.accept <$> str <*> parts)
  | 0x08 => some (.heads <$> str)
  | 0x09 => some (.has <$> str <*> digest)
  | 0x0A => some (.get <$> str <*> digest)
  | 0x0B => some (.reachSet <$> str <*> digests)
  | 0x0C => some (.merge <$> str <*> bytes)
  -- A fact takes at least 37 bytes: a digest, the provenance byte, an empty disown list.
  | 0x0D => some (do let c ← str; .classify c <$> many fact 37 (← u32))
  | 0x0E => some (.encode <$> str)
  | 0x0F => some (.close <$> str)
  | 0x10 => some (do
      let c ← str
      let r ← bytes
      match ← u8 with
      | 0 => pure (.acceptRecord c r none)
      | 1 => pure (.acceptRecord c r (some (← bytes)))
      | _ => failure)
  | _ => none

end Parser

/-- The status a request gets when it cannot be read: `UNKNOWN_OP` or `BAD_REQUEST`. -/
def Request.parse (payload : ByteArray) : Except Code Request :=
  if h : 0 < payload.size then
    match Parser.body payload[0] with
    | none => .error .unknownOp
    | some p =>
      match p.run payload 1 with
      | some q => .ok q
      | none => .error .badRequest
  else .error .badRequest

/-- Whether a request reads back as itself (compared by its bytes). -/
def Request.readsBack (q : Request) : Bool :=
  match Request.parse q.write with
  | .ok q' => q'.write == q.write
  | .error _ => false

open Examples in
#guard [Request.version, .new "chat" group, .open "c" group (.blob (encodeBlob group #[first])),
  .salvage "c" group (.records #[encode first, encode reply]),
  .commit group alice nonce dataMessage, .hash (.ofRec reply), .accept "c" (.ofRec first),
  .heads "c", .has "c" (dig 1), .get "c" (dig 1), .reachSet "c" #[dig 2, dig 1],
  .merge "c" (encodeBlob group #[]),
  .classify "c" #[⟨dig 1, .live, #[dig 2]⟩, ⟨dig 3, .relayed alice, #[]⟩, ⟨dig 4, .imported, #[]⟩],
  .encode "c", .close "c", .acceptRecord "c" (encode first) none,
  .acceptRecord "c" (encode first) (some nonce.bytes)].all Request.readsBack
#guard (match Request.parse ByteArray.empty with | .error .badRequest => true | _ => false)
#guard (match Request.parse ⟨#[0x11]⟩ with | .error .unknownOp => true | _ => false)
#guard (match Request.parse ⟨#[0x01, 0x00]⟩ with | .error .badRequest => true | _ => false)

/-! ## Replies -/

/-- A reply (layouts in the module header). -/
inductive Reply
  /-- `OK` with an empty body. -/
  | ok
  /-- `VERSION`. -/
  | version (protocol : Nat) (build : String)
  /-- `OK` with a digest (`HASH`). -/
  | digest (d : Digest)
  /-- `COMMIT`: the commitment and the opening. -/
  | committed (d : Digest) (opening : ByteArray)
  /-- What `ACCEPT` or `ACCEPT_RECORD` did with record `r`. -/
  | accept (r : Rec) (res : AcceptResult)
  /-- What `OPEN` or `MERGE` did. -/
  | opened (r : Except OpenError Unit)
  /-- What `SALVAGE` did: on success, the dropped and the missing digests. -/
  | salvaged (r : Except OpenError (Array Digest × Array Digest))
  /-- `OK` with a digest list (`HEADS`, `REACH_SET`). -/
  | digests (ds : Array Digest)
  /-- `HAS`. -/
  | has (b : Bool)
  /-- `GET` of a stored record. -/
  | record (r : Rec)
  /-- A status with an empty body: `NOT_FOUND`, `MALFORMED` (`COMMIT`, `ACCEPT_RECORD`),
  `BAD_OPENING`, or a host error. -/
  | code (c : Code)
  /-- `CLASSIFY`. -/
  | classified (ss : Array (Digest × Status))
  /-- `ENCODE`. -/
  | blob (b : ByteArray)

/-- The bytes of a status with an empty body. -/
def Code.write (c : Code) : ByteArray := Write.u8 c.byte

/-- The reply to an `OPEN`, `SALVAGE` or `MERGE` that failed. -/
def writeOpenError : OpenError → ByteArray
  | .malformed => Code.malformed.write
  | .tooLarge => Code.tooLarge.write
  | .wrongChat => Code.wrongChat.write
  | .collision d => Code.collision.write ++ d.bytes
  | .unverifiable u m => Code.unverifiable.write ++ Write.digests u ++ Write.digests m

/-- The payload of a reply: its status byte, then its body. -/
def Reply.write : Reply → ByteArray
  | .ok => Code.ok.write
  | .version n s => Code.ok.write ++ u32be n ++ Write.str s
  | .digest d => Code.ok.write ++ d.bytes
  | .committed d o => Code.ok.write ++ d.bytes ++ Write.bytes o
  | .accept r (.accepted d) => Code.ok.write ++ d.bytes ++ Write.bytes (encode r)
  | .accept _ (.missing ds) => Code.missing.write ++ Write.digests ds
  | .accept _ (.collision d) => Code.collision.write ++ d.bytes
  | .accept _ .wrongChat => Code.wrongChat.write
  | .accept _ .tooLarge => Code.tooLarge.write
  | .opened (.ok ()) => Code.ok.write
  | .opened (.error e) => writeOpenError e
  | .salvaged (.ok (dropped, missing)) =>
    Code.ok.write ++ Write.digests dropped ++ Write.digests missing
  | .salvaged (.error e) => writeOpenError e
  | .digests ds => Code.ok.write ++ Write.digests ds
  | .has b => Code.ok.write ++ Write.u8 (if b then 1 else 0)
  | .record r => Code.ok.write ++ Write.parts (.ofRec r)
  | .code c => c.write
  | .classified ss =>
    ss.foldl (fun acc (d, s) => acc ++ d.bytes ++ Write.status s) (Code.ok.write ++ u32be ss.size)
  | .blob b => Code.ok.write ++ Write.bytes b

open Examples in
#guard (Reply.accept first (.missing #[dig 1])).write == ⟨#[1, 0, 0, 0, 1] ++ (dig 1).bytes.data⟩
-- `ACCEPTED`: the digest, then the record's encoding as `bytes`.
open Examples in
#guard (Reply.accept reply (.accepted (hashRecord reply))).write ==
  ⟨#[0]⟩ ++ (hashRecord reply).bytes ++ u32be 185 ++ encode reply
#guard (Reply.opened (.error (.unverifiable #[] #[]))).write == ⟨#[6, 0, 0, 0, 0, 0, 0, 0, 0]⟩
#guard (Reply.code .chatOpen).write == ⟨#[0x83]⟩

/-! ## The build -/

/-- The Lean sources of the library modules `zrdtd` runs, read when this file is compiled. Any
change to them rebuilds this file, since it imports them all. The read loop, `Zrdtd/Main.lean`,
imports this file, so it reads its own source and passes it to `buildIdOf`. -/
def sources : List String := [
  include_str "Digest.lean", include_str "Sha256.lean", include_str "Record.lean",
  include_str "Encode.lean", include_str "Store.lean", include_str "Provenance.lean",
  include_str "Commit.lean", include_str "Proto.lean"]

/-- The build text of `VERSION`: the package version and the first 16 hex digits of SHA-256 over
`sources` and then `mainSource`, the source of `Zrdtd/Main.lean` (each as `str`). Two builds from
the same sources give the same text. -/
def buildIdOf (mainSource : String) : String :=
  let digest := sha256 ((sources ++ [mainSource]).foldl (fun acc s => acc ++ Write.str s) .empty)
  "zrdt-core 0.1.0 src " ++ String.ofList (digest.toHex.toList.take 16)

/-- The build text without the read loop's source, for the checks in this package. `zrdtd`
reports `buildIdOf` its own source instead. -/
def buildId : String := buildIdOf ""

#guard buildId.length == 36 && buildId != buildIdOf "x"

/-! ## Running requests -/

/-- The open stores, by chat key. -/
abbrev Table := Std.HashMap String CheckedStore

/-- Decode every listed record; `none` if one does not decode. -/
def decodeAll (rs : Array ByteArray) : Option (Array Rec) := rs.mapM decode

/-- `OPEN`: load the input as a store of chat `g`. A blob whose count is too large is refused
before any record is read. -/
def openInput (g : GroupId) : Input → Except OpenError CheckedStore
  | .blob b => if blobTooLarge b then .error .tooLarge else CheckedStore.open g b
  | .records rs =>
    match decodeAll rs with
    | some u => CheckedStore.openRecords g u
    | none => .error .malformed

/-- `SALVAGE`: load what can be accepted of the input as a store of chat `g`. -/
def salvageInput (g : GroupId) : Input → Except OpenError CheckedStore.Salvaged
  | .blob b => if blobTooLarge b then .error .tooLarge else CheckedStore.salvage g b
  | .records rs =>
    match decodeAll rs with
    | some u => CheckedStore.salvageRecords g u
    | none => .error .malformed

/-- Take the store of `chat` out of the table: the store (if any), and the table without it.
The table then holds no reference to the store, so the next change to it can happen in place. -/
def takeOut (t : Table) (chat : String) : Option CheckedStore × Table :=
  (t[chat]?, t.erase chat)

/-- `MERGE`: add the records of blob `b` to `c`. -/
def mergeInput (c : CheckedStore) (b : ByteArray) : Except OpenError CheckedStore :=
  if blobTooLarge b then .error .tooLarge else c.mergeBlob b

/-- Accept record `r` into the store of `chat`. The store is taken out of the table first, so
`accept` can update it in place. -/
def acceptInto (t : Table) (chat : String) (r : Rec) : Reply × Table :=
  match takeOut t chat with
  | (some c, t) =>
    let (res, c) := c.accept r
    (.accept r res, t.insert chat c)
  | (none, t) => (.code .noChat, t)

/-- Answer a request that only reads the store of `chat`. -/
def reading (t : Table) (chat : String) (f : CheckedStore → Reply) : Reply × Table :=
  match t[chat]? with
  | some c => (f c, t)
  | none => (.code .noChat, t)

/-- Carry out a request: the reply and the new table. `build` is the build text of `VERSION`. -/
def run (build : String) (t : Table) : Request → Reply × Table
  | .version => (.version protocolVersion build, t)
  | .new chat g =>
    if t.contains chat then (.code .chatOpen, t) else (.ok, t.insert chat (.empty g))
  | .open chat g i =>
    if t.contains chat then (.code .chatOpen, t)
    else
      match openInput g i with
      | .ok c => (.opened (.ok ()), t.insert chat c)
      | .error e => (.opened (.error e), t)
  | .salvage chat g i =>
    if t.contains chat then (.code .chatOpen, t)
    else
      match salvageInput g i with
      | .ok s => (.salvaged (.ok (s.dropped, s.missing)), t.insert chat s.store)
      | .error e => (.salvaged (.error e), t)
  | .commit g a n m =>
    match commitWithOpening g a n m with
    | some (d, o) => (.committed d o, t)
    | none => (.code .malformed, t)
  | .hash p => (.digest (hashRecord p.toRec), t)
  | .accept chat p => acceptInto t chat p.toRec
  | .acceptRecord chat b o =>
    if !t.contains chat then (.code .noChat, t)
    else
      match decode b with
      | none => (.code .malformed, t)
      | some r =>
        if o.all (openingMatches r.group r.author r.commit) then acceptInto t chat r
        else (.code .badOpening, t)
  | .heads chat => reading t chat fun c => .digests c.headsArray
  | .has chat d => reading t chat fun c => .has (c.has d)
  | .get chat d => reading t chat fun c =>
    match c.get d with
    | some r => .record r
    | none => .code .notFound
  | .reachSet chat ds => reading t chat fun c => .digests (c.reachSet ds).toList.toArray
  | .merge chat b =>
    match takeOut t chat with
    | (some c, t) =>
      match mergeInput c b with
      | .ok e => (.opened (.ok ()), t.insert chat e)
      | .error err => (.opened (.error err), t.insert chat c)
    | (none, t) => (.code .noChat, t)
  | .classify chat facts => reading t chat fun c => .classified (classify c facts).toList.toArray
  | .encode chat => reading t chat fun c => .blob c.encode
  | .close chat => (.ok, t.erase chat)

/-- **`ACCEPT_RECORD` checks before it stores.** If it replies `ACCEPTED` for record `r`, the
bytes it got are exactly `r`'s encoding, and the opening, if one came, is a nonce and message
bytes that hold no field 15 or 200 and whose commitment, by `r`'s author in `r`'s group, is
`r`'s commit. -/
theorem acceptRecord_accepted {build : String} {t t' : Table} {chat : String} {b : ByteArray}
    {o : Option ByteArray} {r : Rec} {d : Digest}
    (h : run build t (.acceptRecord chat b o) = (.accept r (.accepted d), t')) :
    encode r = b ∧ ∀ op ∈ o, ∃ (n : Nonce) (m : ByteArray), op = n.bytes ++ m ∧
      committedBytes m = some m ∧ commit r.group r.author n m = some r.commit := by
  simp only [run] at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · rename_i r' hdec
      split at h
      · rename_i hop
        unfold acceptInto takeOut at h
        split at h
        · simp only [Prod.mk.injEq, Reply.accept.injEq] at h
          obtain ⟨⟨rfl, -⟩, -⟩ := h
          refine ⟨encode_of_decode hdec, fun op hmem => ?_⟩
          subst hmem
          exact openingMatches_spec (by simpa using hop)
        · simp at h
      · simp at h

/-- **`COMMIT`'s opening matches its commitment.** If `COMMIT` replies with commitment `d` and
opening `o`, then `o` passes `openingMatches` for the same group and author: the opening check of
`ACCEPT_RECORD` accepts it with a record of that group, author and commit. -/
theorem commit_openingMatches {build : String} {t t' : Table} {g : GroupId} {a : Aci} {n : Nonce}
    {m : ByteArray} {d : Digest} {o : ByteArray}
    (h : run build t (.commit g a n m) = (.committed d o, t')) : openingMatches g a d o = true := by
  simp only [run] at h
  split at h
  · rename_i d' o' hc
    simp only [Prod.mk.injEq, Reply.committed.injEq] at h
    obtain ⟨⟨rfl, rfl⟩, -⟩ := h
    exact commitWithOpening_matches hc
  · simp at h

/-- Answer one request payload: the reply payload and the new table. A request that cannot be
read gets `UNKNOWN_OP` or `BAD_REQUEST` and changes nothing. -/
def step (build : String) (t : Table) (payload : ByteArray) : ByteArray × Table :=
  match Request.parse payload with
  | .ok q => let (r, t) := run build t q; (r.write, t)
  | .error c => (c.write, t)

/-- Answer a list of request payloads in order, starting from an empty table. -/
def session (payloads : List ByteArray) (build : String := buildId) : List ByteArray :=
  (payloads.foldl (fun (out, t) p => let (r, t) := step build t p; (r :: out, t))
    (([] : List ByteArray), ({} : Table))).1.reverse

open Examples in
-- Open a chat, accept `a1` and then `b1`, read the heads, close.
#guard session [(Request.new "c" group).write, (Request.accept "c" (.ofRec a1)).write,
    (Request.accept "c" (.ofRec b1)).write, (Request.heads "c").write, (Request.close "c").write,
    (Request.heads "c").write] ==
  [Reply.ok.write, (Reply.accept a1 (.accepted (hashRecord a1))).write,
    (Reply.accept b1 (.accepted (hashRecord b1))).write, (Reply.digests #[hashRecord b1]).write,
    Reply.ok.write, (Reply.code .noChat).write]

/-! ## The daemon's state -/

/-- The open stores of the running `zrdtd`. -/
initialize stores : IO.Ref Table ← IO.mkRef {}

/-- `zrdtd`'s only entry point: answer one request payload. `build` is the build text of
`VERSION` (`buildIdOf`). The table is taken out of `stores` while `step` runs, so `step` holds the
only reference to it. -/
def handle (build : String) (payload : ByteArray) : IO ByteArray :=
  stores.modifyGet fun t => step build t payload

end Zrdt.Proto
