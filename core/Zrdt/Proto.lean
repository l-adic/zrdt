import Std.Data.HashMap
import Zrdt.Commit
import Zrdt.Provenance
import Zrdt.Serve

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
- `key`: 33 bytes, an identity public key as libsignal serializes it. `tag`, `rid` (a request
  id): 16 bytes.
- `flag`: `u8`, 0 or 1. Any other value is `BAD_REQUEST`.
- `member`: `aci` ‖ `u8` (1: a `key` follows, 0: none). Members Signal does not send the
  message to (blocked, seen as unregistered) are given with no key.
- `held`: `digest` ‖ `opening`: an opening the host still holds.
- `entry` (in a `SERVE` reply): a kind `u8`, then:
  - `0x00` addressed: the record's encoding (`bytes`) ‖ author copy (`flag`) ‖ `u8` (1: an
    `opening` follows, 0: none);
  - `0x01` after: the record's encoding (`bytes`);
  - `0x02` boundary: a `digest`.

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
| `0x09` | `NO_AUDIENCE` | empty |
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
| `0x07` | `ACCEPT` | `chat` ‖ `parts` ‖ `u8` (1: an `opening` follows, 0: none) |
| `0x08` | `HEADS` | `chat` |
| `0x09` | `HAS` | `chat` ‖ `digest` |
| `0x0A` | `GET` | `chat` ‖ `digest` |
| `0x0B` | `REACH_SET` | `chat` ‖ from (`digests`) |
| `0x0C` | `MERGE` | `chat` ‖ store blob (`bytes`) |
| `0x0D` | `CLASSIFY` | `chat` ‖ a `u32` count ‖ that many `fact`s |
| `0x0E` | `ENCODE` | `chat` |
| `0x0F` | `CLOSE` | `chat` |
| `0x10` | `ACCEPT_RECORD` | `chat` ‖ record (`bytes`) ‖ `u8` (1: an `opening` follows, 0: none) |
| `0x11` | `AUDIENCE` | a `u32` count ‖ that many `member`s |
| `0x12` | `SERVE` | `chat` ‖ own `aci` ‖ requester `aci` ‖ requester `key` ‖ `rid` ‖ since (`digests`) ‖ responder since (`digests`) ‖ `u8` mode (0 catch-up, 1 per-digest) ‖ wanted (`digests`, mode 1 only) ‖ export (`flag`) ‖ strict (`flag`) ‖ live (`digests`) ‖ disown (`digests`) ‖ a `u32` count ‖ that many `held` |
| `0x13` | `ADDRESSED` | `chat` ‖ `aci` ‖ `key` |

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
  `COLLISION`, `WRONG_CHAT`, `TOO_LARGE`, `NO_CHAT`, `BAD_OPENING`, `NO_AUDIENCE`.
- `ACCEPT_RECORD`: as `ACCEPT`, and also `MALFORMED`.
- `AUDIENCE`: `OK`: the field-201 value (`bytes`); `TOO_LARGE`, `MALFORMED`.
- `SERVE`: `OK`: the header (requester `aci` ‖ `tag` of the requester `key` ‖ `rid`) ‖ a `u32`
  count ‖ that many `entry`s; `NO_CHAT`.
- `ADDRESSED`: `OK`: `digests`; `NO_CHAT`.
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
- `ACCEPT` with an opening, and `ACCEPT_RECORD` with one: the opening's commitment under the
  record's group and author must be the record's commit, and it must hold no field 15 or 200
  (`openingMatches`), otherwise `BAD_OPENING`. Its committed bytes must hold exactly one field
  201 whose value is a well-formed audience (`Serve.audienceOf`: 1 to 256 entries, strictly
  increasing by ACI), otherwise `NO_AUDIENCE`: every record message carries its audience. Both
  are checked before the store is touched. If the record is then accepted (now or before), its
  audience is recorded for `ADDRESSED` and `SERVE` (docs/JOIN_PLAN.md §4.2). Without an opening,
  nothing is recorded. Order of checks: `NO_CHAT`, `BAD_OPENING`, `NO_AUDIENCE`, then `accept`'s.
- `ACCEPT_RECORD`: accept a record that came as bytes (relayed or imported), optionally with its
  opening. The bytes must be exactly a record's encoding, otherwise `MALFORMED`. Then as
  `ACCEPT`. Order of checks: `NO_CHAT`, `MALFORMED`, `BAD_OPENING`, `NO_AUDIENCE`, then
  `accept`'s.
- `AUDIENCE` → `OK`: the value of `DataMessage` field 201 for the given members, which the host
  sets as `zrdtAudience` before `COMMIT` (docs/JOIN_PLAN.md §3.2, §4.1): each member's `aci` and
  the `tag` of its key (`Serve.keyTag`, the first 16 bytes of SHA-256(`"zrdtK1"` ‖ key)), or 16
  zero bytes for a member given with no key, sorted by ACI. The host includes the author itself,
  with its own key. The value always passes `Serve.parseAudience` (`run_audience`). `TOO_LARGE`:
  more than 256 members. `MALFORMED`: no members, or an ACI given twice.
- `SERVE` → `OK`: the reply to a member's request (docs/JOIN_PLAN.md §5, `Serve.serve`). The
  responder's state: its own ACI, its `live` digests and its disown set. The request: the
  requester's ACI (the Signal-authenticated sender) and the identity key this device holds for it
  now, the request's id, its `since` and this device's own `since` for that account (joined),
  catch-up or the wanted digests, the export flag and the strict flag. `held`: the openings the
  host holds for stored records; `zrdtd` adds the audiences it recorded. Every opening in the
  reply opens a stored record and its own committed audience seats the requester's ACI under the
  tag of the given key (`run_serve_content`). The header carries the requester's ACI, that tag
  and the request id: the host sends the reply only to that ACI, and seals the bytes after the
  header to exactly that key (`sendZrdtServed`, docs/JOIN_PLAN.md §4.3). `SERVE` changes nothing.
  Entries come sorted by digest.
- `ADDRESSED` → `OK`: the stored records whose recorded audience seats this ACI under the tag of
  this key, sorted: the openings the host should load for `SERVE`.
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
- `VERSION`: the protocol is 3. The build text names the package version and the first 16 hex
  digits of SHA-256 over the Lean sources of the modules `zrdtd` runs, `Zrdtd/Main.lean`
  included (`buildIdOf`).

## The table of open stores

`NEW`, `OPEN` and `SALVAGE` put a store under a chat key that is not in use (otherwise
`CHAT_OPEN`), with no recorded audiences. After that, only `ACCEPT`, `ACCEPT_RECORD` and `MERGE`
change the store, and only `ACCEPT` and `ACCEPT_RECORD` with an opening record audiences; `CLOSE`
removes both. So under one chat key a store and its audiences only grow, until `CLOSE`. A failed
`OPEN`, `SALVAGE`, `MERGE`, `ACCEPT` or `ACCEPT_RECORD` changes nothing. `CLOSE` on a chat key that
is not in use replies `OK`. The audiences are not in the store blob: after `OPEN`, the host
re-sends with `ACCEPT_RECORD` the openings it holds (a stored record is accepted again, and its
audience recorded).

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
  | badOpening | noAudience | badRequest | unknownOp | noChat | chatOpen
deriving DecidableEq, Repr

/-- The byte of each status. -/
def Code.byte : Code → UInt8
  | .ok => 0x00 | .missing => 0x01 | .collision => 0x02 | .wrongChat => 0x03
  | .tooLarge => 0x04 | .malformed => 0x05 | .unverifiable => 0x06 | .notFound => 0x07
  | .badOpening => 0x08 | .noAudience => 0x09
  | .badRequest => 0x80 | .unknownOp => 0x81 | .noChat => 0x82 | .chatOpen => 0x83

/-- The name of each status, as in the module header. -/
def Code.name : Code → String
  | .ok => "OK" | .missing => "MISSING" | .collision => "COLLISION"
  | .wrongChat => "WRONG_CHAT" | .tooLarge => "TOO_LARGE" | .malformed => "MALFORMED"
  | .unverifiable => "UNVERIFIABLE" | .notFound => "NOT_FOUND" | .badOpening => "BAD_OPENING"
  | .noAudience => "NO_AUDIENCE" | .badRequest => "BAD_REQUEST"
  | .unknownOp => "UNKNOWN_OP" | .noChat => "NO_CHAT" | .chatOpen => "CHAT_OPEN"

/-- Every status. -/
def Code.all : List Code :=
  [.ok, .missing, .collision, .wrongChat, .tooLarge, .malformed, .unverifiable, .notFound,
    .badOpening, .noAudience, .badRequest, .unknownOp, .noChat, .chatOpen]

/-- The status with this byte, if any. -/
def Code.ofByte? (b : UInt8) : Option Code := Code.all.find? (·.byte == b)

#guard Code.ofByte? 0x83 == some .chatOpen
#guard Code.ofByte? 0x08 == some .badOpening
#guard Code.ofByte? 0x09 == some .noAudience
#guard Code.ofByte? 0x0A == none
-- Every status has its own byte.
#guard (Code.all.map Code.byte).eraseDups.length == Code.all.length

/-- The op names, in op-byte order: `0x01` is `VERSION`, `0x13` is `ADDRESSED`. -/
def opNames : Array String :=
  #["VERSION", "NEW", "OPEN", "SALVAGE", "COMMIT", "HASH", "ACCEPT", "HEADS", "HAS", "GET",
    "REACH_SET", "MERGE", "CLASSIFY", "ENCODE", "CLOSE", "ACCEPT_RECORD", "AUDIENCE", "SERVE",
    "ADDRESSED"]

/-- The name of the op with this byte, if any. -/
def opName? (b : UInt8) : Option String := if b = 0 then none else opNames[b.toNat - 1]?

#guard opName? 0x0B == some "REACH_SET"
#guard opName? 0x10 == some "ACCEPT_RECORD"
#guard opName? 0x13 == some "ADDRESSED"
#guard opName? 0x00 == none && opName? 0x14 == none

/-- The protocol version. It changes when a request or reply layout changes. Version 2: the
`ACCEPT` and `COMMIT` replies carry the record bytes and the opening; `ACCEPT_RECORD` is new.
Version 3 (docs/JOIN_PLAN.md §10.2): `ACCEPT` takes an optional opening; an opening must carry an
audience (`NO_AUDIENCE`); `AUDIENCE`, `SERVE` and `ADDRESSED` are new. -/
def protocolVersion : Nat := 3

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

/-- A `key`: 33 bytes. -/
def key : Parser ByteArray := take 33

/-- A `rid` (request id): 16 bytes. -/
def rid : Parser ByteArray := take 16

/-- A `flag`: 0 or 1. -/
def flag : Parser Bool := do
  match ← u8 with
  | 0 => pure false
  | 1 => pure true
  | _ => failure

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

/-- The body of a `SERVE` request (layout in the module header). -/
structure ServeRequest where
  /-- The responder's own ACI. -/
  own : Aci
  /-- The Signal-authenticated sender of the request. -/
  requester : Aci
  /-- The identity key this device holds for the requester now (33 bytes). -/
  key : ByteArray
  /-- The request id (16 bytes). -/
  rid : ByteArray
  /-- The request's `since`. -/
  since : Array Digest
  /-- This device's own `since` for the requester's account. -/
  ownSince : Array Digest
  /-- `none`: catch-up. `some ds`: the wanted digests. -/
  wanted : Option (Array Digest)
  /-- An export: refuse disappearing and view-once content. -/
  forExport : Bool
  /-- Strict mode: content only in author copies. -/
  strict : Bool
  /-- The digests this device holds `live`. -/
  live : Array Digest
  /-- This device's disown set. -/
  disown : Array Digest
  /-- The openings the host holds, by digest. -/
  held : Array (Digest × ByteArray)

/-- The request `SERVE` answers. -/
def ServeRequest.query (sr : ServeRequest) : Serve.Query :=
  { aci := sr.requester, key := sr.key, since := sr.since, ownSince := sr.ownSince,
    wanted := sr.wanted, forExport := sr.forExport, strict := sr.strict }

/-- The requester of `SERVE`'s query is the request's. -/
@[simp] theorem ServeRequest.query_aci (sr : ServeRequest) : sr.query.aci = sr.requester := rfl

/-- The key of `SERVE`'s query is the request's. -/
@[simp] theorem ServeRequest.query_key (sr : ServeRequest) : sr.query.key = sr.key := rfl

/-- The responder's own state. A store `zrdtd` holds is closed, so its boundary is empty. -/
def ServeRequest.me (sr : ServeRequest) : Serve.Me :=
  { aci := sr.own, live := sr.live.foldl (·.insert ·) ∅,
    disown := sr.disown.foldl (·.insert ·) ∅ }

/-- What the responder holds outside the store: the audiences `zrdtd` recorded, and the openings
the host passed (a later opening for the same digest replaces an earlier one). -/
def ServeRequest.heldMap (sr : ServeRequest)
    (auds : Std.ExtTreeMap Digest (Array Serve.Seat) compare) : Serve.HeldMap :=
  sr.held.foldl (init := auds.map fun _ a => ({ audience := some a } : Serve.Held)) fun m (d, o) =>
    m.insert d { m.getD d {} with opening := some o }

/-- A request (ops in the module header). -/
inductive Request
  | version
  | new (chat : String) (group : GroupId)
  | «open» (chat : String) (group : GroupId) (input : Input)
  | salvage (chat : String) (group : GroupId) (input : Input)
  | commit (group : GroupId) (author : Aci) (nonce : Nonce) (dataMessage : ByteArray)
  | hash (parts : Parts)
  | accept (chat : String) (parts : Parts) (opening : Option ByteArray)
  | heads (chat : String)
  | has (chat : String) (d : Digest)
  | get (chat : String) (d : Digest)
  | reachSet (chat : String) (start : Array Digest)
  | merge (chat : String) (blob : ByteArray)
  | classify (chat : String) (facts : Array Fact)
  | encode (chat : String)
  | close (chat : String)
  | acceptRecord (chat : String) (record : ByteArray) (opening : Option ByteArray)
  | audience (members : Array (Aci × Option ByteArray))
  | serve (chat : String) (req : ServeRequest)
  | addressed (chat : String) (aci : Aci) (key : ByteArray)

/-- The op byte and name of each request. -/
def Request.op : Request → UInt8 × String
  | .version => (0x01, "VERSION") | .new .. => (0x02, "NEW") | .open .. => (0x03, "OPEN")
  | .salvage .. => (0x04, "SALVAGE") | .commit .. => (0x05, "COMMIT")
  | .hash .. => (0x06, "HASH") | .accept .. => (0x07, "ACCEPT") | .heads .. => (0x08, "HEADS")
  | .has .. => (0x09, "HAS") | .get .. => (0x0A, "GET") | .reachSet .. => (0x0B, "REACH_SET")
  | .merge .. => (0x0C, "MERGE") | .classify .. => (0x0D, "CLASSIFY")
  | .encode .. => (0x0E, "ENCODE") | .close .. => (0x0F, "CLOSE")
  | .acceptRecord .. => (0x10, "ACCEPT_RECORD") | .audience .. => (0x11, "AUDIENCE")
  | .serve .. => (0x12, "SERVE") | .addressed .. => (0x13, "ADDRESSED")

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

/-- `flag`. -/
def flag (b : Bool) : ByteArray := u8 (if b then 1 else 0)

/-- An optional item: `u8` 0, or `u8` 1 and the item. -/
def opt {α : Type} (w : α → ByteArray) : Option α → ByteArray
  | none => u8 0
  | some x => u8 1 ++ w x

/-- `member`. -/
def member (m : Aci × Option ByteArray) : ByteArray := m.1.bytes ++ opt id m.2

/-- The body of a `SERVE` request after the chat key. -/
def serveRequest (sr : ServeRequest) : ByteArray :=
  sr.own.bytes ++ sr.requester.bytes ++ sr.key ++ sr.rid ++ digests sr.since ++
    digests sr.ownSince ++ opt digests sr.wanted ++ flag sr.forExport ++ flag sr.strict ++
    digests sr.live ++ digests sr.disown ++
    sr.held.foldl (fun acc (d, o) => acc ++ d.bytes ++ bytes o) (u32be sr.held.size)

/-- `entry`, in a `SERVE` reply. -/
def entry : Serve.Entry → ByteArray
  | .addressed r o ac => u8 0 ++ bytes (encode r) ++ flag ac ++ opt bytes o
  | .after r => u8 1 ++ bytes (encode r)
  | .boundary d => u8 2 ++ d.bytes

/-- The entries of a `SERVE` reply: a count, then each `entry`. The host seals exactly these
bytes. -/
def entries (es : List Serve.Entry) : ByteArray :=
  es.foldl (fun acc e => acc ++ entry e) (u32be es.length)

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
    | .accept c p o => Write.str c ++ Write.parts p ++ Write.opt Write.bytes o
    | .heads c | .encode c | .close c => Write.str c
    | .has c d | .get c d => Write.str c ++ d.bytes
    | .reachSet c ds => Write.str c ++ Write.digests ds
    | .merge c b => Write.str c ++ Write.bytes b
    | .classify c fs => fs.foldl (fun acc f => acc ++ Write.fact f) (Write.str c ++ u32be fs.size)
    | .acceptRecord c r o => Write.str c ++ Write.bytes r ++ Write.opt Write.bytes o
    | .audience ms => ms.foldl (fun acc m => acc ++ Write.member m) (u32be ms.size)
    | .serve c sr => Write.str c ++ Write.serveRequest sr
    | .addressed c a k => Write.str c ++ a.bytes ++ k

#guard (Request.close "x").write == ⟨#[0x0F, 0, 0, 0, 1, 0x78]⟩
-- `Request.op` and `opNames` agree.
#guard [Request.version, .heads "c", .close "c", .acceptRecord "c" .empty none, .audience #[],
  .addressed "c" Aci.zero .empty].all fun q => opName? q.op.1 == some q.op.2

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

/-- An optional item after a `u8` 0 or 1. -/
def opt {α : Type} (item : Parser α) : Parser (Option α) := do
  match ← u8 with
  | 0 => pure none
  | 1 => some <$> item
  | _ => failure

/-- `member`. -/
def member : Parser (Aci × Option ByteArray) := do
  let a ← aci
  let k ← opt key
  pure (a, k)

/-- `held`. -/
def held : Parser (Digest × ByteArray) := do
  let d ← digest
  let o ← bytes
  pure (d, o)

/-- The body of a `SERVE` request after the chat key. -/
def serveRequest : Parser ServeRequest := do
  let own ← aci
  let requester ← aci
  let key ← key
  let rid ← rid
  let since ← digests
  let ownSince ← digests
  let wanted ← opt digests
  let forExport ← flag
  let strict ← flag
  let live ← digests
  let disown ← digests
  -- A held item takes at least 36 bytes: a digest and an empty opening's length.
  let held ← many held 36 (← u32)
  pure { own, requester, key, rid, since, ownSince, wanted, forExport, strict, live, disown, held }

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
  | 0x07 => some (.accept <$> str <*> parts <*> opt bytes)
  | 0x08 => some (.heads <$> str)
  | 0x09 => some (.has <$> str <*> digest)
  | 0x0A => some (.get <$> str <*> digest)
  | 0x0B => some (.reachSet <$> str <*> digests)
  | 0x0C => some (.merge <$> str <*> bytes)
  -- A fact takes at least 37 bytes: a digest, the provenance byte, an empty disown list.
  | 0x0D => some (do let c ← str; .classify c <$> many fact 37 (← u32))
  | 0x0E => some (.encode <$> str)
  | 0x0F => some (.close <$> str)
  | 0x10 => some (.acceptRecord <$> str <*> bytes <*> opt bytes)
  -- A member takes at least 17 bytes: an ACI and the key byte.
  | 0x11 => some (do .audience <$> many member 17 (← u32))
  | 0x12 => some (.serve <$> str <*> serveRequest)
  | 0x13 => some (.addressed <$> str <*> aci <*> key)
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
  .commit group alice nonce dataMessage, .hash (.ofRec reply), .accept "c" (.ofRec first) none,
  .accept "c" (.ofRec first) (some nonce.bytes), .audience #[(alice, some ⟨Array.replicate 33 1⟩),
    (bob, none)],
  .serve "c"
    { own := alice, requester := bob, key := ⟨Array.replicate 33 2⟩,
      rid := ⟨Array.replicate 16 7⟩, since := #[dig 1], ownSince := #[], wanted := some #[dig 2],
      forExport := true, strict := false, live := #[dig 3], disown := #[dig 4],
      held := #[(dig 3, nonce.bytes)] },
  .serve "c"
    { own := alice, requester := bob, key := ⟨Array.replicate 33 2⟩,
      rid := ⟨Array.replicate 16 7⟩, since := #[], ownSince := #[dig 1], wanted := none,
      forExport := false, strict := true, live := #[], disown := #[], held := #[] },
  .addressed "c" bob ⟨Array.replicate 33 2⟩,
  .heads "c", .has "c" (dig 1), .get "c" (dig 1), .reachSet "c" #[dig 2, dig 1],
  .merge "c" (encodeBlob group #[]),
  .classify "c" #[⟨dig 1, .live, #[dig 2]⟩, ⟨dig 3, .relayed alice, #[]⟩, ⟨dig 4, .imported, #[]⟩],
  .encode "c", .close "c", .acceptRecord "c" (encode first) none,
  .acceptRecord "c" (encode first) (some nonce.bytes)].all Request.readsBack
#guard (match Request.parse ByteArray.empty with | .error .badRequest => true | _ => false)
#guard (match Request.parse ⟨#[0x14]⟩ with | .error .unknownOp => true | _ => false)
#guard (match Request.parse ⟨#[0x01, 0x00]⟩ with | .error .badRequest => true | _ => false)

/-! ## Replies -/

/-- The header of a `SERVE` reply: where the host sends it and the key it seals it to. -/
structure ServeHeader where
  /-- The requester's ACI: the only destination of the reply. -/
  aci : Aci
  /-- The tag of the key `SERVE` checked (`Serve.keyTag`): the host seals to a key with this tag. -/
  tag : Array UInt8
  /-- The request id. -/
  rid : ByteArray
deriving DecidableEq

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
  /-- `AUDIENCE`: the field-201 value. -/
  | audience (b : ByteArray)
  /-- `SERVE`: the header (requester, key tag, request id) and the entries. -/
  | served (header : ServeHeader) (entries : List Serve.Entry)

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
  | .audience b => Code.ok.write ++ Write.bytes b
  | .served h es => Code.ok.write ++ h.aci.bytes ++ ⟨h.tag⟩ ++ h.rid ++ Write.entries es

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
  include_str "Commit.lean", include_str "Serve.lean", include_str "Proto.lean"]

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

/-- One open chat: its store, and the audiences `zrdtd` recorded from openings it checked
(docs/JOIN_PLAN.md §4.2), by digest. -/
structure Chat where
  /-- The store. -/
  store : CheckedStore
  /-- The audience of each stored record whose opening came with `ACCEPT` or `ACCEPT_RECORD`. -/
  audiences : Std.ExtTreeMap Digest (Array Serve.Seat) compare := ∅

/-- The open chats, by chat key. -/
abbrev Table := Std.HashMap String Chat

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

/-- Take the chat `chat` out of the table: the chat (if any), and the table without it. The table
then holds no reference to the store, so the next change to it can happen in place. -/
def takeOut (t : Table) (chat : String) : Option Chat × Table :=
  (t[chat]?, t.erase chat)

/-- `MERGE`: add the records of blob `b` to `c`. -/
def mergeInput (c : CheckedStore) (b : ByteArray) : Except OpenError CheckedStore :=
  if blobTooLarge b then .error .tooLarge else c.mergeBlob b

/-- The audiences after `accept` gave `res` for a record whose checked opening has audience
`aud`: recorded under the digest if the record is stored. -/
def recordAudience (auds : Std.ExtTreeMap Digest (Array Serve.Seat) compare) (res : AcceptResult)
    (aud : Option (Array Serve.Seat)) : Std.ExtTreeMap Digest (Array Serve.Seat) compare :=
  match res, aud with
  | .accepted d, some a => auds.insert d a
  | _, _ => auds

/-- Accept record `r` into the store of `chat`, and record `aud` if it is stored. The chat is
taken out of the table first, so `accept` can update the store in place. -/
def acceptInto (t : Table) (chat : String) (r : Rec) (aud : Option (Array Serve.Seat)) :
    Reply × Table :=
  match takeOut t chat with
  | (some ⟨c, auds⟩, t) =>
    let p := c.accept r
    (.accept r p.1, t.insert chat ⟨p.2, recordAudience auds p.1 aud⟩)
  | (none, t) => (.code .noChat, t)

/-- Accept record `r` into the store of `chat` with an optional opening: the opening must match
the record (`BAD_OPENING`) and carry an audience (`NO_AUDIENCE`), checked before the store is
touched. -/
def acceptChecked (t : Table) (chat : String) (r : Rec) : Option ByteArray → Reply × Table
  | none => acceptInto t chat r none
  | some o =>
    if !openingMatches r.group r.author r.commit o then (.code .badOpening, t)
    else
      match Serve.audienceOf o with
      | none => (.code .noAudience, t)
      | some aud => acceptInto t chat r (some aud)

/-- Answer a request that only reads the chat `chat`. -/
def reading (t : Table) (chat : String) (f : Chat → Reply) : Reply × Table :=
  match t[chat]? with
  | some c => (f c, t)
  | none => (.code .noChat, t)

/-- `AUDIENCE`: the field-201 value for these members, sorted by ACI; a member with no key gets
the zero tag. The result is checked with `Serve.parseAudience` before it is returned, so it is
never a value `ACCEPT` would refuse. -/
def audienceReply (ms : Array (Aci × Option ByteArray)) : Reply :=
  if Serve.maxAudience < ms.size then .code .tooLarge
  else
    let seats := (ms.qsort fun x y => compare x.1 y.1 == .lt).map fun (a, k) =>
      ({ aci := a, tag := (k.map Serve.keyTag).getD Serve.zeroTag } : Serve.Seat)
    let b := Serve.writeAudience seats
    if (Serve.parseAudience b).isSome then .audience b else .code .malformed

/-- `SERVE` on chat `ch`. -/
def serveReply (ch : Chat) (sr : ServeRequest) : Reply :=
  .served ⟨sr.requester, Serve.keyTag sr.key, sr.rid⟩
    (Serve.serve ch.store sr.me (sr.heldMap ch.audiences) sr.query)

/-- `ADDRESSED`: the stored records whose recorded audience seats `aci` under `key`. -/
def addressedOf (ch : Chat) (aci : Aci) (key : ByteArray) : Array Digest :=
  (ch.audiences.toList.filterMap fun (d, aud) =>
    if Serve.seats aud aci key then some d else none).toArray

/-- Carry out a request: the reply and the new table. `build` is the build text of `VERSION`. -/
def run (build : String) (t : Table) : Request → Reply × Table
  | .version => (.version protocolVersion build, t)
  | .new chat g =>
    if t.contains chat then (.code .chatOpen, t) else (.ok, t.insert chat { store := .empty g })
  | .open chat g i =>
    if t.contains chat then (.code .chatOpen, t)
    else
      match openInput g i with
      | .ok c => (.opened (.ok ()), t.insert chat { store := c })
      | .error e => (.opened (.error e), t)
  | .salvage chat g i =>
    if t.contains chat then (.code .chatOpen, t)
    else
      match salvageInput g i with
      | .ok s => (.salvaged (.ok (s.dropped, s.missing)), t.insert chat { store := s.store })
      | .error e => (.salvaged (.error e), t)
  | .commit g a n m =>
    match commitWithOpening g a n m with
    | some (d, o) => (.committed d o, t)
    | none => (.code .malformed, t)
  | .hash p => (.digest (hashRecord p.toRec), t)
  | .accept chat p o =>
    if !t.contains chat then (.code .noChat, t) else acceptChecked t chat p.toRec o
  | .acceptRecord chat b o =>
    if !t.contains chat then (.code .noChat, t)
    else
      match decode b with
      | none => (.code .malformed, t)
      | some r => acceptChecked t chat r o
  | .heads chat => reading t chat fun c => .digests c.store.headsArray
  | .has chat d => reading t chat fun c => .has (c.store.has d)
  | .get chat d => reading t chat fun c =>
    match c.store.get d with
    | some r => .record r
    | none => .code .notFound
  | .reachSet chat ds => reading t chat fun c => .digests (c.store.reachSet ds).toList.toArray
  | .merge chat b =>
    match takeOut t chat with
    | (some c, t) =>
      match mergeInput c.store b with
      | .ok e => (.opened (.ok ()), t.insert chat { c with store := e })
      | .error err => (.opened (.error err), t.insert chat c)
    | (none, t) => (.code .noChat, t)
  | .classify chat facts => reading t chat fun c =>
    .classified (classify c.store facts).toList.toArray
  | .encode chat => reading t chat fun c => .blob c.store.encode
  | .close chat => (.ok, t.erase chat)
  | .audience ms => (audienceReply ms, t)
  | .serve chat sr => reading t chat fun c => serveReply c sr
  | .addressed chat a k => reading t chat fun c => .digests (addressedOf c a k)

/-- What `acceptInto` did when it replies `ACCEPTED`: the record is the one given, and the
audience given, if any, is recorded under the digest in the new table. -/
theorem acceptInto_accepted {t t' : Table} {chat : String} {r r' : Rec}
    {aud : Option (Array Serve.Seat)} {d : Digest}
    (h : acceptInto t chat r aud = (.accept r' (.accepted d), t')) :
    r' = r ∧ ∀ a, aud = some a → ∃ ch, t'[chat]? = some ch ∧ ch.audiences[d]? = some a := by
  unfold acceptInto takeOut at h
  split at h
  · simp only [Prod.mk.injEq, Reply.accept.injEq] at h
    obtain ⟨⟨rfl, hres⟩, rfl⟩ := h
    refine ⟨rfl, fun a ha => ⟨_, Std.HashMap.getElem?_insert_self, ?_⟩⟩
    simp only [CheckedStore.accept_fst] at hres
    simp [recordAudience, hres, ha]
  · simp at h

/-- What `acceptChecked` did when it replies `ACCEPTED`: an opening, if one came, matches the
record and carries an audience, which is recorded under the record's digest. -/
theorem acceptChecked_accepted {t t' : Table} {chat : String} {r r' : Rec}
    {o : Option ByteArray} {d : Digest}
    (h : acceptChecked t chat r o = (.accept r' (.accepted d), t')) :
    r' = r ∧ ∀ op ∈ o, openingMatches r.group r.author r.commit op = true ∧
      ∃ aud, Serve.audienceOf op = some aud ∧
        ∃ ch, t'[chat]? = some ch ∧ ch.audiences[d]? = some aud := by
  cases o with
  | none =>
    exact ⟨(acceptInto_accepted h).1, by simp⟩
  | some op =>
    simp only [acceptChecked] at h
    split at h
    · simp at h
    · rename_i hm
      split at h
      · simp at h
      · rename_i aud ha
        obtain ⟨rfl, hrec⟩ := acceptInto_accepted h
        refine ⟨rfl, fun op' hop => ?_⟩
        cases hop
        simp only [Bool.not_eq_true', Bool.not_eq_false] at hm
        exact ⟨hm, aud, ha, hrec aud rfl⟩

/-- **`ACCEPT_RECORD` checks before it stores.** If it replies `ACCEPTED` for record `r`, the
bytes it got are exactly `r`'s encoding, and the opening, if one came, is a nonce and message
bytes that hold no field 15 or 200 and whose commitment, by `r`'s author in `r`'s group, is
`r`'s commit; it carries an audience, and that audience is recorded under `r`'s digest. -/
theorem acceptRecord_accepted {build : String} {t t' : Table} {chat : String} {b : ByteArray}
    {o : Option ByteArray} {r : Rec} {d : Digest}
    (h : run build t (.acceptRecord chat b o) = (.accept r (.accepted d), t')) :
    encode r = b ∧ ∀ op ∈ o, (∃ (n : Nonce) (m : ByteArray), op = n.bytes ++ m ∧
      committedBytes m = some m ∧ commit r.group r.author n m = some r.commit) ∧
      ∃ aud, Serve.audienceOf op = some aud ∧
        ∃ ch, t'[chat]? = some ch ∧ ch.audiences[d]? = some aud := by
  simp only [run] at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · rename_i r' hdec
      obtain ⟨rfl, hop⟩ := acceptChecked_accepted h
      refine ⟨encode_of_decode hdec, fun op hmem => ?_⟩
      obtain ⟨hm, rest⟩ := hop op hmem
      exact ⟨openingMatches_spec hm, rest⟩

/-- **`ACCEPT` checks an opening before it stores.** If it replies `ACCEPTED`, the record is the
one given, and an opening, if one came, matches it and carries an audience, which is recorded
under the record's digest. -/
theorem accept_accepted {build : String} {t t' : Table} {chat : String} {p : Parts}
    {o : Option ByteArray} {r : Rec} {d : Digest}
    (h : run build t (.accept chat p o) = (.accept r (.accepted d), t')) :
    r = p.toRec ∧ ∀ op ∈ o, openingMatches r.group r.author r.commit op = true ∧
      ∃ aud, Serve.audienceOf op = some aud ∧
        ∃ ch, t'[chat]? = some ch ∧ ch.audiences[d]? = some aud := by
  simp only [run] at h
  split at h
  · simp at h
  · obtain ⟨rfl, hop⟩ := acceptChecked_accepted h
    exact ⟨rfl, hop⟩

/-- **`SERVE` sends content only to an account its author addressed, under the checked key.** If
`SERVE` replies with header `h` and entries `es`, nothing changed; the header names the requester,
the tag of the key `SERVE` checked, and the request id; and every opening in the entries opens a
record of the chat's store, with its own committed audience seating the header's ACI under that
key. The host sends the reply only to `h.aci` and seals the entries to a key whose tag is
`h.tag` (docs/JOIN_PLAN.md §4.3), so the account and the key checked are the ones that can read
the content. -/
theorem run_serve_content {build : String} {t t' : Table} {chat : String} {sr : ServeRequest}
    {h : ServeHeader} {es : List Serve.Entry}
    (hr : run build t (.serve chat sr) = (.served h es, t')) :
    t' = t ∧ h.aci = sr.requester ∧ h.tag = Serve.keyTag sr.key ∧ h.rid = sr.rid ∧
      ∃ ch, t[chat]? = some ch ∧ ∀ r o ac, Serve.Entry.addressed r o ac ∈ es →
        ∃ d, ch.store.get d = some r ∧ ∀ op, o = some op →
          openingMatches r.group r.author r.commit op = true ∧
          ∃ aud, Serve.audienceOf op = some aud ∧ Serve.seats aud h.aci sr.key = true := by
  simp only [run, reading] at hr
  split at hr
  · rename_i ch hch
    simp only [serveReply, Prod.mk.injEq, Reply.served.injEq] at hr
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hr
    refine ⟨rfl, rfl, rfl, rfl, ch, hch, fun r o ac he => ?_⟩
    obtain ⟨d, hget, hop⟩ := Serve.serve_content he
    refine ⟨d, hget, fun op hop' => ?_⟩
    have h1 := hop op hop'
    rw [ServeRequest.query_aci, ServeRequest.query_key] at h1
    exact h1
  · simp at hr

/-- **`AUDIENCE` gives a value `ACCEPT` takes.** Its field-201 value is a well-formed audience,
and nothing changed. -/
theorem run_audience {build : String} {t t' : Table} {ms : Array (Aci × Option ByteArray)}
    {b : ByteArray} (h : run build t (.audience ms) = (.audience b, t')) :
    t' = t ∧ (Serve.parseAudience b).isSome = true := by
  simp only [run, audienceReply, Prod.mk.injEq] at h
  obtain ⟨h, rfl⟩ := h
  refine ⟨rfl, ?_⟩
  split at h
  · simp at h
  · split at h
    · rename_i hp
      simp only [Reply.audience.injEq] at h
      rw [← h]
      exact hp
    · simp at h

/-- **`ADDRESSED` lists only records whose recorded audience seats the account.** Every digest
it returns is stored with a recorded audience that seats `aci` under the tag of `key`. -/
theorem run_addressed {build : String} {t t' : Table} {chat : String} {a : Aci}
    {k : ByteArray} {ds : Array Digest}
    (h : run build t (.addressed chat a k) = (.digests ds, t')) :
    t' = t ∧ ∃ ch, t[chat]? = some ch ∧ ∀ d ∈ ds,
      ∃ aud, ch.audiences[d]? = some aud ∧ Serve.seats aud a k = true := by
  simp only [run, reading] at h
  split at h
  · rename_i ch hch
    simp only [Prod.mk.injEq, Reply.digests.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨rfl, ch, hch, fun d hd => ?_⟩
    simp only [addressedOf, List.mem_toArray, List.mem_filterMap] at hd
    obtain ⟨⟨d', aud⟩, hmem, hf⟩ := hd
    split at hf
    · rename_i hs
      simp only [Option.some.injEq] at hf
      subst hf
      exact ⟨aud, Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some.1 hmem, hs⟩
    · simp at hf
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

/-! ### `run_serve_content` on a real request

A table holding Alice's message to herself (`Serve.Examples.selfMsg`), and her own `SERVE`
request for her account: the reply holds the message with its opening, as an author copy. So the
hypothesis of `run_serve_content` is met, and its content clause is not vacuous. -/

open Serve.Examples in
/-- Chat `"self"`: Alice's message to herself, no audience recorded. -/
def selfTable : Table := (∅ : Table).insert "self" { store := selfStore }

open Serve.Examples in
/-- Alice asks for her own account's catch-up, under her own key; her device holds the opening and
the record `live`. -/
def selfServe : ServeRequest :=
  { own := Examples.alice, requester := Examples.alice, key := keyAlice,
    rid := ⟨Array.replicate 16 0⟩, since := #[], ownSince := #[], wanted := none,
    forExport := false, strict := false, live := #[selfDigest], disown := #[],
    held := #[(selfDigest, selfMsg.2)] }

open Serve.Examples in
example : ∃ h es t', run buildId selfTable (.serve "self" selfServe) = (.served h es, t') ∧
    Serve.Entry.addressed selfMsg.1 (some selfMsg.2) true ∈ es := by
  have hme : selfServe.me = selfMe := by
    simp [ServeRequest.me, selfServe, selfMe]
  have hheld : selfServe.heldMap ∅ = selfHeld := by
    have hm : (∅ : Std.ExtTreeMap Digest (Array Serve.Seat) compare).map
        (fun _ a => ({ audience := some a } : Serve.Held)) = ∅ :=
      Std.ExtTreeMap.map_eq_empty_iff.2 rfl
    simp [ServeRequest.heldMap, selfServe, selfHeld, hm]
  have hq : selfServe.query = rq Examples.alice keyAlice := rfl
  refine ⟨⟨Examples.alice, Serve.keyTag keyAlice, ⟨Array.replicate 16 0⟩⟩,
    Serve.serve selfStore selfServe.me (selfServe.heldMap ∅) selfServe.query, selfTable, ?_, ?_⟩
  · simp only [run, reading, selfTable, Std.HashMap.getElem?_insert_self]
    rfl
  · rw [hme, hheld, hq]
    exact self_served false false

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
#guard session [(Request.new "c" group).write, (Request.accept "c" (.ofRec a1) none).write,
    (Request.accept "c" (.ofRec b1) none).write, (Request.heads "c").write, (Request.close "c").write,
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
