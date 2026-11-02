import Std.Data.HashMap
import Zrdt.Commit
import Zrdt.Provenance
import Zrdt.Serve
import Zrdt.ChatStore

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
- `entry` (in a `SERVE` reply and an `ACCEPT_VIEW` request): a kind `u8`, then:
  - `0x00` addressed: the record's encoding (`bytes`) ‖ author copy (`flag`) ‖ `u8` (1: an
    `opening` follows, 0: none);
  - `0x01` after: the record's encoding (`bytes`);
  - `0x02` boundary: a `digest`.
- `entries`: a `u32` count, then that many `entry`s. A `SERVE` reply's bytes after its 48-byte
  header are `entries`; the requester passes them, once unsealed, to `ACCEPT_VIEW` unchanged.
- `pending` (in an `ACCEPT_VIEW` request): `entries` the host adds after the reply's: the records
  it holds pending (an `ACCEPT` or `ACCEPT_VIEW` result of `MISSING`), a live one as `addressed`
  with its opening, a relayed one as `after`, so a boundary digest they link is kept and they are
  accepted in the same request.
- `result` (in an `ACCEPT_VIEW` reply), one per entry of `entries` and then of `pending`: a
  status byte, then for `OK` the `digest` (the record's, or the boundary digest's), for `MISSING`
  the `digests` that are neither stored nor boundary digests, for `COLLISION` the `digest`,
  otherwise nothing.
- `zrdtS3` (a store blob, in `OPEN`, `SALVAGE`, `MERGE` and the `ENCODE` reply; `Zrdt.ChatStore`):
  `"zrdtS3"` ‖ mode `u8` (0 closed, 1 relative) ‖ a `u32` count ‖ that many (`digest` ‖ voucher
  `aci`), the boundary sorted by digest ‖ a `u32` count ‖ that many (`digest` ‖ field-201 value
  as `bytes`), the recorded audiences sorted by digest ‖ the records as a `zrdtS2` blob
  (docs/PLAN.md §3.4) to the end. A closed blob lists no boundary digest. Only `zrdtS3` is read
  (greenfield).

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
| `0x0A` | `EPHEMERAL` | empty (only as an `ACCEPT_VIEW` result) |
| `0x0B` | `IGNORED` | empty (only as an `ACCEPT_VIEW` result) |
| `0x0C` | `BAD_PIECE` | protocol 5, lane base (section below) |
| `0x0D` | `BAD_APP` | protocol 5, lane base: reason (`u8`) |
| `0x0E` | `BAD_NAME` | protocol 5, lane torrent |
| `0x10` | `PUSH_REFUSED` | protocol 5, lane git |
| `0x11` | `BAD_OBJECTS` | protocol 5, lane git |
| `0x12` | `OPENINGS_MISSING` | protocol 5, lane git: `digests` |
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
| `0x07` | `ACCEPT` | `chat` ‖ `parts` ‖ `opening` |
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
| `0x14` | `ACCEPT_VIEW` | `chat` ‖ voucher (`aci`) ‖ import (`flag`) ‖ `u8` mode (0 catch-up, 1 per-digest) ‖ `entries` ‖ `pending` |
| `0x15` | `LINKABLE` | `chat` ‖ live (`digests`) |
| `0x16` | `NEW_RELATIVE` | `chat` ‖ `group` |

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
- `ACCEPT_VIEW`: `OK`: a `u32` count ‖ that many `result`s, one per entry, in order; `NO_CHAT`.
- `LINKABLE`: `OK`: `digests`; `NO_CHAT`.
- `NEW_RELATIVE`: `OK`; `CHAT_OPEN`.
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
- `ACCEPT` takes a live record **always with its opening** (docs/JOIN_PLAN.md §4.2), so every
  record it stores has its audience recorded (`accept_accepted`). The opening's commitment under
  the record's group and author must be the record's commit, and it must hold no field 15 or 200
  (`openingMatches`), otherwise `BAD_OPENING`. Its committed bytes must hold exactly one field
  201 whose value is a well-formed audience (`Serve.audienceOf`: 1 to 256 entries, strictly
  increasing by ACI), otherwise `NO_AUDIENCE`: every record message carries its audience. Both
  are checked before the store is touched (`accept_refused`: nothing changes). If the record is
  then accepted (now or before), its audience is recorded for `ADDRESSED` and `SERVE`. Order of
  checks: `NO_CHAT`, `BAD_OPENING`, `NO_AUDIENCE`, then `accept`'s. A record that arrives without
  its content (relayed, imported, or the structure of a `SERVE` reply) goes in with
  `ACCEPT_RECORD` or `ACCEPT_VIEW`.
- `ACCEPT_RECORD`: accept a record that came as bytes (relayed or imported), optionally with its
  opening (checked as `ACCEPT`'s, and its audience recorded); without one it is stored as
  structure only and no audience is recorded. The bytes must be exactly a record's encoding,
  otherwise `MALFORMED`. Order of checks: `NO_CHAT`, `MALFORMED`, `BAD_OPENING`, `NO_AUDIENCE`,
  then `accept`'s.
- `AUDIENCE` → `OK`: the value of `DataMessage` field 201 for the given members, which the host
  sets as `zrdtAudience` before `COMMIT` (docs/JOIN_PLAN.md §3.2, §4.1): each member's `aci` and
  the `tag` of its key (`Serve.keyTag`, the first 16 bytes of SHA-256(`"zrdtK1"` ‖ key)), or 16
  zero bytes for a member given with no key, sorted by ACI. The host includes the author itself,
  with its own key. The value always passes `Serve.parseAudience` (`run_audience`). `TOO_LARGE`:
  more than 256 members. `MALFORMED`: no members, or an ACI given twice.
- `SERVE` → `OK`: the reply to a member's request (docs/JOIN_PLAN.md §5, `Serve.serve`). The
  responder's state: its own ACI, its `live` digests and its disown set (and `zrdtd` adds a
  relative store's own boundary digests). The request: the
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
- `NEW` opens an empty **closed** store; `NEW_RELATIVE` an empty **relative** one, for a device
  that has no store for a group it is a member of (a catch-up, docs/JOIN_PLAN.md §6.1, and a
  re-add, §6.5). A relative store takes boundary digests; a closed one never does. Every op works
  on both. On a relative store: a link resolves if it is stored or a boundary digest, so
  `MISSING` lists the links that are neither; `HEADS` lists the stored digests and the boundary
  digests that no stored record links; `HAS` and `GET` know stored records only; `SERVE` also
  serves the store's own boundary digests (`Serve.Me.boundary`).
- `ACCEPT_VIEW` → `OK`: the requester takes a `SERVE` reply (docs/JOIN_PLAN.md §4.4). The host
  passes only replies that passed §4.4's checks (sealed to this account, solicited by this
  device, from a responder whose key has not changed), with the responder as voucher, the mode of
  the request it sent (0 catch-up, 1 per-digest), and after the reply's entries its own pending
  records (`pending`). Every entry is checked first, as `ACCEPT_RECORD` checks: the record bytes
  must decode (`MALFORMED`), an opening must match (`BAD_OPENING`) and carry an audience
  (`NO_AUDIENCE`), and with the import flag (an export from another account, A9) an opening must
  not disappear or be view-once (`EPHEMERAL`). A refused entry changes nothing. Then a relative
  store takes each boundary entry's digest as a boundary digest vouched by the voucher (the first
  voucher of a digest stays); a closed store takes none (`IGNORED`, unless the digest is a stored
  record). Then the records of the entries that passed are accepted as one batch, in whatever
  order lets their links resolve (`acceptAll`). **Boundary admission:** in per-digest mode, a
  boundary digest the request added is then dropped again unless it is stored or a stored record
  links it (one stored before, or one accepted in this request: a pending record that links it).
  So a per-digest reply never adds a head that is not a stored record (`acceptView_heads`,
  `acceptView_boundary_linked`); a digest asked for by name that nothing links stays unknown. A
  catch-up reply describes the responder's whole frontier (`Serve.serve_boundary`: a boundary
  entry is linked by a served record or is a head of the responder), so in catch-up mode every
  boundary entry is kept. The audience of each checked opening is recorded for a record that is
  stored. A record whose digest is a boundary digest is accepted like any other: it replaces the
  digest (promotion). The result of a record entry is what `ACCEPT` would reply for it now (`OK`
  with its digest only if it is stored, `acceptView_accepted`); of a boundary entry, `OK` with
  the digest if it is now a boundary digest or a stored record, `IGNORED` (a closed store, or
  dropped in per-digest mode) or `TOO_LARGE` (the boundary holds 2^24 - 1 digests). The
  author-copy flag is not read: provenance stays host state (A8). The host keeps as pending every
  record whose result is `MISSING` and asks for the digests listed.
- `LINKABLE` → `OK`: the digests a new record of this device may link (`COMMIT`'s links, docs/
  JOIN_PLAN.md §6.2). A closed store: its heads (`HEADS`, as A7). A relative store: the heads that
  are stored records in `live`, which the host fills with the digests it holds `live` (its own
  included) or as an author copy; never a boundary digest or a relayed head (`run_linkable`).
- `MISSING`: the store is unchanged; the list holds exactly the links that are not stored (nor,
  in a relative store, boundary digests), and is never empty.
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
- `OPEN` of a blob, `SALVAGE` of a blob, `ENCODE`: the blob is `zrdtS3`. A closed blob loads
  with exactly the checks of `CheckedStore.open` and `salvage` (on its records part); a relative
  one loads its records over its boundary (`RelStore.load`). The audiences come back with the
  store, for stored records only (`ChatStore.encode_reopens`: the blob of a store reopens as exactly
  that store and its audiences). `MERGE` into a closed store reads the blob's records part as
  before (a relative blob's records that link its boundary are `UNVERIFIABLE`); into a relative
  store, it adds the blob's records and boundary. `MERGE` records the blob's audience of each
  record stored in the merged store that has none recorded; a recorded audience stays
  (`run_merge_audiences`). `ENCODE` writes only well-formed audiences, which is every one `zrdtd`
  records (`Serve.audienceOf_valid`).
- `VERSION`: the protocol is 5 (protocol 4's layouts unchanged, and the apps' below). The build
  text names the package version and the first 16 hex digits of SHA-256 over the Lean sources of
  the modules `zrdtd` runs, `Zrdtd/Main.lean` included (`buildIdOf`).

## The table of open stores

`NEW`, `NEW_RELATIVE`, `OPEN` and `SALVAGE` put a store under a chat key that is not in use
(otherwise `CHAT_OPEN`), with the audiences of the blob (none for `NEW`, `NEW_RELATIVE` and a
record list). After that, only `ACCEPT`, `ACCEPT_RECORD`, `ACCEPT_VIEW` and `MERGE` change the
store, and only `ACCEPT`, `ACCEPT_RECORD` and `ACCEPT_VIEW` with an opening, and `MERGE` (the
blob's), record audiences; `CLOSE` removes both. So under one chat key a store and its audiences only grow, until `CLOSE`,
and a store stays closed or relative. A failed `OPEN`, `SALVAGE`, `MERGE`, `ACCEPT` or
`ACCEPT_RECORD` changes nothing. `CLOSE` on a chat key that is not in use replies `OK`. The
audiences are in the store blob (`zrdtS3`); the host may still re-send with `ACCEPT_RECORD` the
openings it holds (a stored record is accepted again, and its audience recorded).

`ACCEPT`, `ACCEPT_RECORD`, `ACCEPT_VIEW` and `MERGE` take the store out of the table before they
change it, and put the result back. For `ACCEPT` the table then holds no second reference to the
store, so `accept` updates it in place. `MERGE` keeps the original to put back if the merge fails;
the merged store shares most of its tree with it.

## Protocol 5: the apps (docs/apps/BUILD_M1.md)

`zrdtd` answers with `Zrdt.Apps.handle`, which runs every protocol-4 request as above (on a piece
key, see `Zrdt.Apps`) and sends op bytes `0x17`-`0x2F` to the apps: lane base `0x17`-`0x1F`
(`Zrdt.AppBase`), lane torrent `0x20`-`0x27` (`Zrdt.Torrent`), lane git `0x28`-`0x2F`
(`Zrdt.Git`). Op bytes `0x00` and `0x30`-`0xFF` stay unknown, and so does an op byte of a lane's
range that the lane does not define. `VERSION` says 5.

Each lane writes the byte layouts of its ops here, in its own section, when its code lands; this
header is then authoritative for them. Until then docs/apps/BUILD_M1.md §B is the reference.

### [BEGIN lane base] protocol-5 field types; `BAD_PIECE`, `BAD_APP`; ops `0x17`-`0x1F`

(Not yet written.)

### [END lane base]

### [BEGIN lane torrent] `BAD_NAME`; ops `0x20`-`0x27`

Lane torrent, `Zrdt.Torrent`. A torrent is one file in a Signal group's channel `bt/files`
(`AppBase.channelId sg "bt" "files"`): an announcement A with body `"zbt1"` and a piece store of
its bytes. The **app manifest** (the descriptor's last field) is `"zbtF1"` ‖ name (`str`) ‖ `u64` L.
A **name** is one path component (`Torrent.safeComponent`): 1-255 bytes of UTF-8; not `.` or `..`;
no `/ \ : < > " | ? *`, NUL, byte below `0x20` or DEL; no leading or trailing space or dot; not
CON, PRN, AUX, NUL, COM1-9 or LPT1-9 in any case, with or without an extension.

`BAD_NAME` (`0x0E`): empty body; the name is not a safe path component.

| Op | Name | Request body | Reply |
|---|---|---|---|
| `0x20` | `BT_BUILD` | channel (`group`) ‖ author (`aci`) ‖ store `nonce` ‖ `u8` k ‖ audience (`bytes`) ‖ name (`str`) ‖ pointers (`bytes`) ‖ stream (`bytes`) | `OK`: A's committed bytes (`bytes`) ‖ the piece digests in index order (`u32` N ‖ N `digest`s); `BAD_NAME`; `BAD_APP` 6 |
| `0x21` | `BT_FILE` | piece key (`str`) | `OK`: name (`str`) ‖ `u64` L; `BAD_APP` 7 (another app's store), 5 (the manifest does not parse, or is not exactly that of its name and of the descriptor's L); `BAD_NAME`; `NO_CHAT` |

`0x22`-`0x27` are reserved. Both ops only read the state.

**`BT_BUILD`** is pure. It refuses an unsafe name (`BAD_NAME`), then (`BAD_APP` 6) k ∉ {20, 10},
an empty stream or one over 64 pieces, pointers over 16 KiB, and an audience `ACCEPT` would refuse.
Its message is `AppBase.appMessage` of: the audience; app `"bt"`; channel `"files"`; body `"zbt1"`;
the descriptor (store nonce, L, k, the piece digests, the app manifest); the pointers if not empty.
The digest of piece i is that of `AppBase.pieceRecord` of slice i under the context any bind of A
gives (channel, author, store nonce, audience). Before it answers, it reads the message back as
`PIECES_BIND` will (`appHeader`, `committedBytes`, `Descriptor.parse`, the limits) and refuses
(`BAD_APP` 6) if any check fails, so an `OK` always binds.

### [END lane torrent]

### [BEGIN lane git] `PUSH_REFUSED`, `BAD_OBJECTS`, `OPENINGS_MISSING`; ops `0x28`-`0x2F`

(Not yet written.)

### [END lane git]
-/

namespace Zrdt.Proto

/-! ## Status bytes and op bytes -/

/-- The first byte of a reply (table in the module header). -/
inductive Code
  | ok | missing | collision | wrongChat | tooLarge | malformed | unverifiable | notFound
  | badOpening | noAudience | ephemeral | ignored | badRequest | unknownOp | noChat | chatOpen
  -- Protocol 5 (docs/apps/BUILD_M1.md §B.4): fixed here for all lanes; changed only by lane base.
  | badPiece | badApp | badName | pushRefused | badObjects | openingsMissing
deriving DecidableEq, Repr

/-- The byte of each status. -/
def Code.byte : Code → UInt8
  | .ok => 0x00 | .missing => 0x01 | .collision => 0x02 | .wrongChat => 0x03
  | .tooLarge => 0x04 | .malformed => 0x05 | .unverifiable => 0x06 | .notFound => 0x07
  | .badOpening => 0x08 | .noAudience => 0x09 | .ephemeral => 0x0A | .ignored => 0x0B
  | .badRequest => 0x80 | .unknownOp => 0x81 | .noChat => 0x82 | .chatOpen => 0x83
  | .badPiece => 0x0C | .badApp => 0x0D | .badName => 0x0E | .pushRefused => 0x10
  | .badObjects => 0x11 | .openingsMissing => 0x12

/-- The name of each status, as in the module header. -/
def Code.name : Code → String
  | .ok => "OK" | .missing => "MISSING" | .collision => "COLLISION"
  | .wrongChat => "WRONG_CHAT" | .tooLarge => "TOO_LARGE" | .malformed => "MALFORMED"
  | .unverifiable => "UNVERIFIABLE" | .notFound => "NOT_FOUND" | .badOpening => "BAD_OPENING"
  | .noAudience => "NO_AUDIENCE" | .ephemeral => "EPHEMERAL" | .ignored => "IGNORED"
  | .badRequest => "BAD_REQUEST"
  | .unknownOp => "UNKNOWN_OP" | .noChat => "NO_CHAT" | .chatOpen => "CHAT_OPEN"
  | .badPiece => "BAD_PIECE" | .badApp => "BAD_APP" | .badName => "BAD_NAME"
  | .pushRefused => "PUSH_REFUSED" | .badObjects => "BAD_OBJECTS"
  | .openingsMissing => "OPENINGS_MISSING"

/-- Every status. -/
def Code.all : List Code :=
  [.ok, .missing, .collision, .wrongChat, .tooLarge, .malformed, .unverifiable, .notFound,
    .badOpening, .noAudience, .ephemeral, .ignored, .badRequest, .unknownOp, .noChat, .chatOpen,
    .badPiece, .badApp, .badName, .pushRefused, .badObjects, .openingsMissing]

/-- The protocol-5 statuses (docs/apps/BUILD_M1.md §B.4). -/
def Code.v5 : List Code :=
  [.badPiece, .badApp, .badName, .pushRefused, .badObjects, .openingsMissing]

/-- The status with this byte, if any. -/
def Code.ofByte? (b : UInt8) : Option Code := Code.all.find? (·.byte == b)

#guard Code.ofByte? 0x83 == some .chatOpen
#guard Code.ofByte? 0x08 == some .badOpening
#guard Code.ofByte? 0x09 == some .noAudience
#guard Code.ofByte? 0x0B == some .ignored
#guard Code.ofByte? 0x0C == some .badPiece && Code.ofByte? 0x12 == some .openingsMissing
#guard Code.ofByte? 0x0F == none && Code.ofByte? 0x13 == none
-- Every status has its own byte.
#guard (Code.all.map Code.byte).eraseDups.length == Code.all.length

/-- The op names, in op-byte order: `0x01` is `VERSION`, `0x16` is `NEW_RELATIVE`. -/
def opNames : Array String :=
  #["VERSION", "NEW", "OPEN", "SALVAGE", "COMMIT", "HASH", "ACCEPT", "HEADS", "HAS", "GET",
    "REACH_SET", "MERGE", "CLASSIFY", "ENCODE", "CLOSE", "ACCEPT_RECORD", "AUDIENCE", "SERVE",
    "ADDRESSED", "ACCEPT_VIEW", "LINKABLE", "NEW_RELATIVE"]

/-! ### Protocol-5 op names (docs/apps/BUILD_M1.md §B)

One list per lane, `(op byte, name)`, each in its own section; only the owning lane edits it. The
`#guard` in each section keeps the lane inside its range. -/

-- [BEGIN lane base] op names, 0x17-0x1F
/-- Lane base's op names (`Zrdt.AppBase`). -/
def baseOpNames : List (UInt8 × String) :=
  [(0x17, "CHANNEL"), (0x18, "PIECES_BIND"), (0x19, "PIECE_ACCEPT"), (0x1A, "PIECE_OPENING"),
    (0x1B, "PIECES_COMPLETE"), (0x1C, "ASSEMBLE")]
#guard baseOpNames.all fun (b, _) => 0x17 ≤ b && b ≤ 0x1F
-- [END lane base]

-- [BEGIN lane torrent] op names, 0x20-0x27
/-- Lane torrent's op names (`Zrdt.Torrent`). -/
def torrentOpNames : List (UInt8 × String) := [(0x20, "BT_BUILD"), (0x21, "BT_FILE")]
#guard torrentOpNames.all fun (b, _) => 0x20 ≤ b && b ≤ 0x27
-- [END lane torrent]

-- [BEGIN lane git] op names, 0x28-0x2F
/-- Lane git's op names (`Zrdt.Git`). -/
def gitOpNames : List (UInt8 × String) := []
#guard gitOpNames.all fun (b, _) => 0x28 ≤ b && b ≤ 0x2F
-- [END lane git]

/-- Every protocol-5 op name. -/
def v5OpNames : List (UInt8 × String) := baseOpNames ++ torrentOpNames ++ gitOpNames

/-- The name of the op with this byte, if any: protocol 4's, or a lane's. -/
def opName? (b : UInt8) : Option String :=
  if b = 0 then none else (opNames[b.toNat - 1]?).orElse fun _ => v5OpNames.lookup b

#guard opName? 0x0B == some "REACH_SET"
#guard opName? 0x10 == some "ACCEPT_RECORD"
#guard opName? 0x13 == some "ADDRESSED"
#guard opName? 0x14 == some "ACCEPT_VIEW" && opName? 0x16 == some "NEW_RELATIVE"
#guard opName? 0x00 == none && opName? 0x30 == none

/-- The protocol version. It changes when a request or reply layout changes. Version 2: the
`ACCEPT` and `COMMIT` replies carry the record bytes and the opening; `ACCEPT_RECORD` is new.
Version 3 (docs/JOIN_PLAN.md §10.2): an opening must carry an audience (`NO_AUDIENCE`);
`AUDIENCE`, `SERVE`, `ADDRESSED`, `ACCEPT_VIEW`, `LINKABLE` and `NEW_RELATIVE` are new; store
blobs are `zrdtS3`. Version 4: `ACCEPT` always takes the opening (a live record always has its
audience recorded); `ACCEPT_VIEW` takes a mode (catch-up or per-digest) and the host's pending
records, and in per-digest mode keeps only the boundary digests a stored record links. Version 5
(docs/apps/BUILD_M1.md): the apps' ops from `0x17` and statuses `0x0C`-`0x12`; every protocol-4
layout is unchanged. -/
def protocolVersion : Nat := 5

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

/-- The responder's own state: from the request, and the store's own boundary digests (empty
for a closed store). -/
def ServeRequest.me (sr : ServeRequest) (boundary : DigestSet := ∅) : Serve.Me :=
  { aci := sr.own, live := sr.live.foldl (·.insert ·) ∅,
    disown := sr.disown.foldl (·.insert ·) ∅, boundary }

/-- What the responder holds outside the store: the audiences `zrdtd` recorded, and the openings
the host passed (a later opening for the same digest replaces an earlier one). -/
def ServeRequest.heldMap (sr : ServeRequest)
    (auds : Std.ExtTreeMap Digest (Array Serve.Seat) compare) : Serve.HeldMap :=
  sr.held.foldl (init := auds.map fun _ a => ({ audience := some a } : Serve.Held)) fun m (d, o) =>
    m.insert d { m.getD d {} with opening := some o }

/-- An entry of an `ACCEPT_VIEW` request: an entry of a `SERVE` reply, as the requester got it
(the record as bytes, not yet decoded). -/
inductive ViewEntry
  /-- A record sent to this account, its author-copy flag, and its opening if one came. -/
  | addressed (record : ByteArray) (authorCopy : Bool) (opening : Option ByteArray)
  /-- A record's structure, no content. -/
  | after (record : ByteArray)
  /-- A digest only. -/
  | boundary (d : Digest)

/-- A request (ops in the module header). -/
inductive Request
  | version
  | new (chat : String) (group : GroupId)
  | «open» (chat : String) (group : GroupId) (input : Input)
  | salvage (chat : String) (group : GroupId) (input : Input)
  | commit (group : GroupId) (author : Aci) (nonce : Nonce) (dataMessage : ByteArray)
  | hash (parts : Parts)
  | accept (chat : String) (parts : Parts) (opening : ByteArray)
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
  | acceptView (chat : String) (voucher : Aci) (forImport perDigest : Bool)
      (entries pending : Array ViewEntry)
  | linkable (chat : String) (live : Array Digest)
  | newRelative (chat : String) (group : GroupId)

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
  | .acceptView .. => (0x14, "ACCEPT_VIEW") | .linkable .. => (0x15, "LINKABLE")
  | .newRelative .. => (0x16, "NEW_RELATIVE")

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

/-- An entry of an `ACCEPT_VIEW` request: the bytes `entry` writes for a `SERVE` reply. -/
def viewEntry : ViewEntry → ByteArray
  | .addressed r ac o => u8 0 ++ bytes r ++ flag ac ++ opt bytes o
  | .after r => u8 1 ++ bytes r
  | .boundary d => u8 2 ++ d.bytes

/-- The entries of an `ACCEPT_VIEW` request: a count, then each entry. -/
def viewEntries (es : Array ViewEntry) : ByteArray :=
  es.foldl (fun acc e => acc ++ viewEntry e) (u32be es.size)

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
    | .accept c p o => Write.str c ++ Write.parts p ++ Write.bytes o
    | .heads c | .encode c | .close c => Write.str c
    | .has c d | .get c d => Write.str c ++ d.bytes
    | .reachSet c ds => Write.str c ++ Write.digests ds
    | .merge c b => Write.str c ++ Write.bytes b
    | .classify c fs => fs.foldl (fun acc f => acc ++ Write.fact f) (Write.str c ++ u32be fs.size)
    | .acceptRecord c r o => Write.str c ++ Write.bytes r ++ Write.opt Write.bytes o
    | .audience ms => ms.foldl (fun acc m => acc ++ Write.member m) (u32be ms.size)
    | .serve c sr => Write.str c ++ Write.serveRequest sr
    | .addressed c a k => Write.str c ++ a.bytes ++ k
    | .acceptView c v i pd es ps =>
      Write.str c ++ v.bytes ++ Write.flag i ++ Write.flag pd ++ Write.viewEntries es ++
        Write.viewEntries ps
    | .linkable c ds => Write.str c ++ Write.digests ds
    | .newRelative c g => Write.str c ++ g.bytes

#guard (Request.close "x").write == ⟨#[0x0F, 0, 0, 0, 1, 0x78]⟩
-- `Request.op` and `opNames` agree.
#guard [Request.version, .heads "c", .close "c", .acceptRecord "c" .empty none, .audience #[],
  .addressed "c" Aci.zero .empty, .acceptView "c" Aci.zero false false #[] #[], .linkable "c" #[],
  .newRelative "c" GroupId.zero].all fun q => opName? q.op.1 == some q.op.2

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

/-- An entry of an `ACCEPT_VIEW` request. -/
def viewEntry : Parser ViewEntry := do
  match ← u8 with
  | 0 => do
    let r ← bytes
    let ac ← flag
    let o ← opt bytes
    pure (.addressed r ac o)
  | 1 => .after <$> bytes
  | 2 => .boundary <$> digest
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
  | 0x07 => some (.accept <$> str <*> parts <*> bytes)
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
  -- An entry takes at least 5 bytes: the kind and a record's length.
  | 0x14 => some (do
    let c ← str
    let v ← aci
    let i ← flag
    let pd ← flag
    let es ← many viewEntry 5 (← u32)
    let ps ← many viewEntry 5 (← u32)
    pure (.acceptView c v i pd es ps))
  | 0x15 => some (.linkable <$> str <*> digests)
  | 0x16 => some (.newRelative <$> str <*> group)
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
  .commit group alice nonce dataMessage, .hash (.ofRec reply), .accept "c" (.ofRec first) .empty,
  .accept "c" (.ofRec first) nonce.bytes, .audience #[(alice, some ⟨Array.replicate 33 1⟩),
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
  .acceptRecord "c" (encode first) (some nonce.bytes),
  .acceptView "c" alice true false #[.addressed (encode first) true (some nonce.bytes),
    .addressed (encode reply) false none, .after (encode first), .boundary (dig 5)] #[],
  .acceptView "c" alice false true #[.boundary (dig 5)] #[.after (encode first)],
  .acceptView "c" bob false false #[] #[], .linkable "c" #[dig 1, dig 2],
  .newRelative "n" group].all
  Request.readsBack
#guard (match Request.parse ByteArray.empty with | .error .badRequest => true | _ => false)
#guard (match Request.parse ⟨#[0x17]⟩ with | .error .unknownOp => true | _ => false)
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

/-- What `ACCEPT_VIEW` did with one entry. -/
inductive ViewResult
  /-- A record entry: what `accept` says for the record in the store after the request. -/
  | record (res : AcceptResult)
  /-- A boundary entry: the digest is now a boundary digest or a stored record. -/
  | known (d : Digest)
  /-- Refused: `MALFORMED`, `BAD_OPENING`, `NO_AUDIENCE`, `EPHEMERAL` (a record entry, before the
  store is touched), `IGNORED` or `TOO_LARGE` (a boundary entry). -/
  | code (c : Code)

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
  /-- `ACCEPT_VIEW`: one result per entry. -/
  | viewed (results : Array ViewResult)

/-- The bytes of a status with an empty body. -/
def Code.write (c : Code) : ByteArray := Write.u8 c.byte

/-- The reply to an `OPEN`, `SALVAGE` or `MERGE` that failed. -/
def writeOpenError : OpenError → ByteArray
  | .malformed => Code.malformed.write
  | .tooLarge => Code.tooLarge.write
  | .wrongChat => Code.wrongChat.write
  | .collision d => Code.collision.write ++ d.bytes
  | .unverifiable u m => Code.unverifiable.write ++ Write.digests u ++ Write.digests m

/-- One result of an `ACCEPT_VIEW` reply: a status byte, then `OK`: the digest; `MISSING`: the
`digests` neither stored nor in the boundary; `COLLISION`: the `digest`; otherwise nothing. -/
def ViewResult.write : ViewResult → ByteArray
  | .record (.accepted d) | .known d => Code.ok.write ++ d.bytes
  | .record (.missing ds) => Code.missing.write ++ Write.digests ds
  | .record (.collision d) => Code.collision.write ++ d.bytes
  | .record .wrongChat => Code.wrongChat.write
  | .record .tooLarge => Code.tooLarge.write
  | .code c => c.write

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
  | .viewed rs => rs.foldl (fun acc x => acc ++ x.write) (Code.ok.write ++ u32be rs.size)

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
  include_str "Commit.lean", include_str "RelStore.lean", include_str "Serve.lean",
  include_str "ChatStore.lean", include_str "Proto.lean"]

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
  /-- The store: closed, or relative (created by `NEW_RELATIVE`, or opened from a relative
  blob). -/
  store : ChatStore
  /-- The audience of each stored record whose opening came with `ACCEPT`, `ACCEPT_RECORD` or
  `ACCEPT_VIEW`, or that the chat's blob carried at `OPEN`. -/
  audiences : AudTable := ∅

/-- The open chats, by chat key. -/
abbrev Table := Std.HashMap String Chat

/-- Decode every listed record; `none` if one does not decode. -/
def decodeAll (rs : Array ByteArray) : Option (Array Rec) := rs.mapM decode

/-- `OPEN`: load the input as a chat of group `g`: a `zrdtS3` blob (`openChat`), or a list of
records as a closed store. A records blob whose count is too large is refused before any record
is read. -/
def openInput (g : GroupId) : Input → Except OpenError Chat
  | .blob b => (fun (s, auds) => ({ store := s, audiences := auds } : Chat)) <$> openChat g b
  | .records rs =>
    match decodeAll rs with
    | some u => (fun c => ({ store := .closed c } : Chat)) <$> CheckedStore.openRecords g u
    | none => .error .malformed

/-- `SALVAGE`: load what can be accepted of the input as a chat of group `g`, and the dropped and
missing digests. -/
def salvageInput (g : GroupId) : Input → Except OpenError (Chat × Array Digest × Array Digest)
  | .blob b =>
    (fun sv => (({ store := sv.store, audiences := sv.audiences } : Chat), sv.dropped, sv.missing))
      <$> salvageChat g b
  | .records rs =>
    match decodeAll rs with
    | some u =>
      (fun sv => (({ store := .closed sv.store } : Chat), sv.dropped, sv.missing)) <$>
        CheckedStore.salvageRecords g u
    | none => .error .malformed

/-- Take the chat `chat` out of the table: the chat (if any), and the table without it. The table
then holds no reference to the store, so the next change to it can happen in place. -/
def takeOut (t : Table) (chat : String) : Option Chat × Table :=
  (t[chat]?, t.erase chat)

/-- `MERGE`: add the records of the `zrdtS3` blob `b` to the store `s` (`mergeChat`): the merged
store and the blob's audiences. -/
def mergeInput (s : ChatStore) (b : ByteArray) : Except OpenError (ChatStore × AudTable) :=
  mergeChat s b

/-- The audiences after `accept` gave `res` for a record whose checked opening has audience
`aud`: recorded under the digest if the record is stored. -/
def recordAudience (auds : AudTable) (res : AcceptResult) (aud : Option (Array Serve.Seat)) :
    AudTable :=
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
    (Serve.serve ch.store.raw (sr.me ch.store.boundaryDigests) (sr.heldMap ch.audiences) sr.query)

/-- `ADDRESSED`: the stored records whose recorded audience seats `aci` under `key`. -/
def addressedOf (ch : Chat) (aci : Aci) (key : ByteArray) : Array Digest :=
  (ch.audiences.toList.filterMap fun (d, aud) =>
    if Serve.seats aud aci key then some d else none).toArray

/-! ### `ACCEPT_VIEW` (docs/JOIN_PLAN.md §4.4, §6.2) -/

/-- What one `ACCEPT_VIEW` entry asks for, after its own checks. -/
inductive ViewItem
  /-- Accept this record; record this audience (from its checked opening) if it is stored. -/
  | record (r : Rec) (aud : Option (Array Serve.Seat))
  /-- Take this boundary digest. -/
  | boundary (d : Digest)
  /-- Refused before the store is touched. -/
  | refused (c : Code)

/-- The checks of one entry, as `ACCEPT_RECORD`'s: the record bytes must decode (`MALFORMED`); an
opening must match the record (`BAD_OPENING`) and carry an audience (`NO_AUDIENCE`); for an
import, it must neither disappear nor be view-once (`EPHEMERAL`, A9). -/
def checkEntry (forImport : Bool) : ViewEntry → ViewItem
  | .boundary d => .boundary d
  | .after b =>
    match decode b with
    | some r => .record r none
    | none => .refused .malformed
  | .addressed b _ o =>
    match decode b with
    | none => .refused .malformed
    | some r =>
      match o with
      | none => .record r none
      | some op =>
        if !openingMatches r.group r.author r.commit op then .refused .badOpening
        else
          match Serve.audienceOf op with
          | none => .refused .noAudience
          | some aud => if forImport && Serve.ephemeral op then .refused .ephemeral
            else .record r (some aud)

open Serve.Examples in
-- An import refuses a disappearing message's opening; a relay takes it. A wrong opening is
-- refused, and so are bytes that are not a record.
#guard [checkEntry true (.addressed (encode timed.1) false (some timed.2)),
    checkEntry false (.addressed (encode timed.1) false (some timed.2)),
    checkEntry false (.addressed (encode later.1) false (some welcome.2)),
    checkEntry false (.after ((encode later.1).push 0))].map (fun
      | .refused c => c.name | .record _ (some _) => "record+audience" | _ => "other") ==
  ["EPHEMERAL", "record+audience", "BAD_OPENING", "MALFORMED"]

/-- The record an item asks to accept. -/
def ViewItem.record? : ViewItem → Option Rec
  | .record r _ => some r
  | _ => none

/-- Take boundary digest `d` vouched by `v`: a relative store adds it (`RelStore.addBoundary`;
nothing changes if its boundary is full); a closed store takes no boundary digest. -/
def takeBoundary (v : Aci) (s : ChatStore) (d : Digest) : ChatStore :=
  match s with
  | .closed _ => s
  | .relative c =>
    match c.addBoundary d v with
    | some c' => .relative c'
    | none => s

/-- Take the boundary digest of an item, if it is one. -/
def takeItem (v : Aci) (s : ChatStore) : ViewItem → ChatStore
  | .boundary d => takeBoundary v s d
  | _ => s

/-- Take the boundary digests of the items, in order. -/
def takeBoundaries (v : Aci) (s : ChatStore) (items : List ViewItem) : ChatStore :=
  items.foldl (takeItem v) s

/-- The store after taking the boundary entries of `items` (vouched by `v`) and accepting their
records as one batch (`ChatStore.acceptAll`), before the per-digest prune. -/
def viewAccepted (s : ChatStore) (v : Aci) (items : List ViewItem) : ChatStore :=
  ((takeBoundaries v s items).acceptAll (items.filterMap ViewItem.record?).toArray).1

/-- The store `ACCEPT_VIEW` leaves: `viewAccepted`, and in per-digest mode without the new boundary
digests that are stored nowhere and linked by no stored record (`ChatStore.prune`). -/
def viewStore (s : ChatStore) (v : Aci) (perDigest : Bool) (items : List ViewItem) : ChatStore :=
  if perDigest then (viewAccepted s v items).prune s.boundary else viewAccepted s v items

open Examples in
-- Per-digest, a boundary digest no record links is not kept; catch-up keeps it.
#guard [true, false].map (fun pd =>
  (viewStore (.relative (.empty group)) alice pd [.boundary (dig 7)]).boundaryDigests.toList) ==
  [[], [dig 7]]

/-- `ACCEPT_VIEW` on chat `ch`: take the boundary entries (a relative store only), then accept the
record entries that pass their checks as one batch (`ChatStore.acceptAll`); in per-digest mode,
drop again the new boundary digests that no stored record links (`viewStore`). Record the
audiences of the checked openings for the records that are stored. The reply has one result per
entry: for a record, what `accept` says for it in the final store; for a boundary digest, `known`
if it is now a boundary digest or a stored record, otherwise `IGNORED` (closed store, or dropped in
per-digest mode) or `TOO_LARGE` (the boundary is full). -/
def acceptView (ch : Chat) (v : Aci) (forImport perDigest : Bool) (es : Array ViewEntry) :
    Array ViewResult × Chat :=
  let items := es.toList.map (checkEntry forImport)
  let s2 := viewAccepted ch.store v items
  let s3 := viewStore ch.store v perDigest items
  let result : ViewItem → ViewResult := fun
    | .record r _ => .record (s3.accept r).1
    | .boundary d =>
      if s3.has d || s3.boundary.contains d then .known d
      else if s2.boundary.contains d || !s3.isRelative then .code .ignored
      else .code .tooLarge
    | .refused c => .code c
  let auds := items.foldl (init := ch.audiences) fun auds it =>
    match it with
    | .record r (some a) => recordAudience auds (s3.accept r).1 (some a)
    | _ => auds
  ((items.map result).toArray, { store := s3, audiences := auds })

/-- Carry out a request: the reply and the new table. `build` is the build text of `VERSION`. -/
def run (build : String) (t : Table) : Request → Reply × Table
  | .version => (.version protocolVersion build, t)
  | .new chat g =>
    if t.contains chat then (.code .chatOpen, t)
    else (.ok, t.insert chat { store := .closed (.empty g) })
  | .newRelative chat g =>
    if t.contains chat then (.code .chatOpen, t)
    else (.ok, t.insert chat { store := .relative (.empty g) })
  | .open chat g i =>
    if t.contains chat then (.code .chatOpen, t)
    else
      match openInput g i with
      | .ok ch => (.opened (.ok ()), t.insert chat ch)
      | .error e => (.opened (.error e), t)
  | .salvage chat g i =>
    if t.contains chat then (.code .chatOpen, t)
    else
      match salvageInput g i with
      | .ok (ch, dropped, missing) => (.salvaged (.ok (dropped, missing)), t.insert chat ch)
      | .error e => (.salvaged (.error e), t)
  | .commit g a n m =>
    match commitWithOpening g a n m with
    | some (d, o) => (.committed d o, t)
    | none => (.code .malformed, t)
  | .hash p => (.digest (hashRecord p.toRec), t)
  | .accept chat p o =>
    if !t.contains chat then (.code .noChat, t) else acceptChecked t chat p.toRec (some o)
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
      | .ok (e, blobAuds) =>
        (.opened (.ok ()), t.insert chat
          { store := e, audiences := mergeAudiences e c.audiences blobAuds })
      | .error err => (.opened (.error err), t.insert chat c)
    | (none, t) => (.code .noChat, t)
  | .classify chat facts => reading t chat fun c =>
    .classified (c.store.classify facts).toList.toArray
  | .encode chat => reading t chat fun c => .blob (encodeChat c.store c.audiences)
  | .close chat => (.ok, t.erase chat)
  | .audience ms => (audienceReply ms, t)
  | .serve chat sr => reading t chat fun c => serveReply c sr
  | .addressed chat a k => reading t chat fun c => .digests (addressedOf c a k)
  | .acceptView chat v i pd es ps =>
    match takeOut t chat with
    | (some ch, t) =>
      let (rs, ch') := acceptView ch v i pd (es ++ ps)
      (.viewed rs, t.insert chat ch')
    | (none, t) => (.code .noChat, t)
  | .linkable chat live => reading t chat fun c =>
    .digests (c.store.linkable (live.foldl (·.insert ·) ∅))

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

/-- **`ACCEPT` takes a live record with its opening, and records its audience.** If it replies
`ACCEPTED`, the record is the one given, the opening matches it (its commitment, by the record's
author in the record's group, is the record's commit, and it holds no field 15 or 200), and the
audience its committed bytes carry is recorded under the record's digest: every record `ACCEPT`
stores has its audience. -/
theorem accept_accepted {build : String} {t t' : Table} {chat : String} {p : Parts}
    {o : ByteArray} {r : Rec} {d : Digest}
    (h : run build t (.accept chat p o) = (.accept r (.accepted d), t')) :
    r = p.toRec ∧ openingMatches r.group r.author r.commit o = true ∧
      ∃ aud, Serve.audienceOf o = some aud ∧
        ∃ ch, t'[chat]? = some ch ∧ ch.audiences[d]? = some aud := by
  simp only [run] at h
  split at h
  · simp at h
  · obtain ⟨rfl, hop⟩ := acceptChecked_accepted h
    exact ⟨rfl, hop o rfl⟩

/-- **`ACCEPT` refuses an opening that does not match or carries no audience, and changes
nothing.** A reply with an empty body leaves the table as it was; it is `NO_CHAT`, `BAD_OPENING`
(the opening does not match the record) or `NO_AUDIENCE` (it matches, but its committed bytes hold
no well-formed field 201). -/
theorem accept_refused {build : String} {t t' : Table} {chat : String} {p : Parts}
    {o : ByteArray} {c : Code} (h : run build t (.accept chat p o) = (.code c, t')) :
    t' = t ∧ (c = .noChat ∨
      (c = .badOpening ∧ openingMatches p.toRec.group p.toRec.author p.toRec.commit o = false) ∨
      (c = .noAudience ∧ openingMatches p.toRec.group p.toRec.author p.toRec.commit o = true ∧
        Serve.audienceOf o = none)) := by
  simp only [run] at h
  split at h
  · simp only [Prod.mk.injEq, Reply.code.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, .inl rfl⟩
  · rename_i hnc
    simp only [acceptChecked] at h
    split at h
    · rename_i hm
      simp only [Prod.mk.injEq, Reply.code.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [Bool.not_eq_true'] at hm
      exact ⟨rfl, .inr (.inl ⟨rfl, hm⟩)⟩
    · rename_i hm
      split at h
      · rename_i ha
        simp only [Prod.mk.injEq, Reply.code.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp only [Bool.not_eq_true', Bool.not_eq_false] at hm
        exact ⟨rfl, .inr (.inr ⟨rfl, hm, ha⟩)⟩
      · have hc : t.contains chat = true := by
          cases hb : t.contains chat
          · rw [hb] at hnc; exact absurd rfl hnc
          · rfl
        have hsome : (t[chat]?).isSome := by
          rw [← Std.HashMap.contains_eq_isSome_getElem?]; exact hc
        obtain ⟨ch, hch⟩ := Option.isSome_iff_exists.mp hsome
        unfold acceptInto takeOut at h
        rw [hch] at h
        obtain ⟨st, au⟩ := ch
        simp only [Prod.mk.injEq, reduceCtorEq, false_and] at h

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

/-- **`MERGE` records the blob's audiences, and keeps every recorded one.** If `MERGE` replies
`OK`, the chat's store is the one `mergeChat` gives, every audience recorded before is still
recorded, and a new one is the blob's audience (`mergeChat`'s table) of a record stored in the
merged store that had none. -/
theorem run_merge_audiences {build : String} {t t' : Table} {chat : String} {b : ByteArray}
    (h : run build t (.merge chat b) = (.opened (.ok ()), t')) :
    ∃ ch ch' blobAuds, t[chat]? = some ch ∧ t'[chat]? = some ch' ∧
      mergeChat ch.store b = .ok (ch'.store, blobAuds) ∧
      (∀ (d : Digest) (a : Array Serve.Seat), ch.audiences[d]? = some a →
        ch'.audiences[d]? = some a) ∧
      (∀ (d : Digest) (a : Array Serve.Seat), ch'.audiences[d]? = some a →
        ch.audiences[d]? = some a ∨
          (ch.audiences[d]? = none ∧ ch'.store.has d = true ∧ blobAuds[d]? = some a)) := by
  simp only [run, takeOut] at h
  cases hch : t[chat]? with
  | none => simp [hch] at h
  | some ch =>
    simp only [hch] at h
    cases hm : mergeInput ch.store b with
    | error e => simp [hm] at h
    | ok p =>
      obtain ⟨e, blobAuds⟩ := p
      simp only [hm, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      obtain ⟨keep, only⟩ := mergeAudiences_spec e ch.audiences blobAuds
      exact ⟨ch, _, blobAuds, rfl, Std.HashMap.getElem?_insert_self, hm, keep, only⟩

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

/-! ### What `ACCEPT_VIEW`, `LINKABLE` and `NEW_RELATIVE` guarantee -/

/-- A boundary item comes from a boundary entry with that digest. -/
theorem checkEntry_boundary {imp : Bool} {e : ViewEntry} {d : Digest}
    (h : checkEntry imp e = .boundary d) : e = .boundary d := by
  cases e with
  | boundary d' => simp only [checkEntry, ViewItem.boundary.injEq] at h; rw [h]
  | after b => simp only [checkEntry] at h; split at h <;> simp at h
  | addressed b ac o =>
    simp only [checkEntry] at h
    split at h
    · simp at h
    · cases o with
      | none => simp at h
      | some op =>
        simp only at h
        split at h
        · simp at h
        · split at h
          · simp at h
          · split at h <;> simp at h

/-- A record item comes from a record entry whose bytes decode to it. An audience comes only with
an opening of that entry that matches the record, carries exactly that audience, and, for an
import, neither disappears nor is view-once. -/
theorem checkEntry_record {imp : Bool} {e : ViewEntry} {r : Rec}
    {aud : Option (Array Serve.Seat)} (h : checkEntry imp e = .record r aud) :
    (∃ b, decode b = some r ∧ (e = .after b ∨ ∃ ac o, e = .addressed b ac o)) ∧
    ∀ a, aud = some a → ∃ b ac op, e = .addressed b ac (some op) ∧
      openingMatches r.group r.author r.commit op = true ∧ Serve.audienceOf op = some a ∧
      (imp = true → Serve.ephemeral op = false) := by
  cases e with
  | boundary d => simp [checkEntry] at h
  | after b =>
    simp only [checkEntry] at h
    split at h
    · rename_i r' hd
      simp only [ViewItem.record.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨⟨b, hd, .inl rfl⟩, by simp⟩
    · simp at h
  | addressed b ac o =>
    simp only [checkEntry] at h
    split at h
    · simp at h
    · rename_i r' hd
      cases o with
      | none =>
        simp only [ViewItem.record.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨⟨b, hd, .inr ⟨ac, none, rfl⟩⟩, by simp⟩
      | some op =>
        simp only at h
        split at h
        · simp at h
        · rename_i hm
          split at h
          · simp at h
          · rename_i a' ha
            split at h
            · simp at h
            · rename_i hne
              simp only [ViewItem.record.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              refine ⟨⟨b, hd, .inr ⟨ac, some op, rfl⟩⟩, fun a ha' => ?_⟩
              cases ha'
              refine ⟨b, ac, op, rfl, by simpa using hm, ha, fun hi => ?_⟩
              simpa [hi] using hne

/-- Taking one boundary digest keeps the kind, the chat and the records; the boundary only grows,
by `d` with voucher `v`. -/
theorem takeBoundary_spec (v : Aci) (s : ChatStore) (d : Digest) :
    (takeBoundary v s d).isRelative = s.isRelative ∧ (takeBoundary v s d).raw.map = s.raw.map ∧
    (takeBoundary v s d).raw.group = s.raw.group ∧
    ∀ (x : Digest) (a : Aci), (takeBoundary v s d).boundary[x]? = some a →
      s.boundary[x]? = some a ∨ (x = d ∧ a = v) := by
  cases s with
  | closed c => exact ⟨rfl, rfl, rfl, fun _ _ h => .inl h⟩
  | relative c =>
    simp only [takeBoundary]
    cases hadd : c.addBoundary d v with
    | none => exact ⟨rfl, rfl, rfl, fun _ _ h => .inl h⟩
    | some c' =>
      obtain ⟨hg, hm, -, -, hnew⟩ := RelStore.addBoundary_spec hadd
      exact ⟨rfl, hm, hg, fun x a h => hnew x a h⟩

/-- Taking the boundary items keeps the kind, the chat and the records; every new boundary digest
is one of the items, with voucher `v`. -/
theorem takeBoundaries_spec (v : Aci) (s : ChatStore) (items : List ViewItem) :
    (takeBoundaries v s items).isRelative = s.isRelative ∧
    (takeBoundaries v s items).raw.map = s.raw.map ∧
    (takeBoundaries v s items).raw.group = s.raw.group ∧
    ∀ (x : Digest) (a : Aci), (takeBoundaries v s items).boundary[x]? = some a →
      s.boundary[x]? = some a ∨ (a = v ∧ ViewItem.boundary x ∈ items) := by
  induction items generalizing s with
  | nil => exact ⟨rfl, rfl, rfl, fun _ _ h => .inl h⟩
  | cons it rest ih =>
    have hstep : takeBoundaries v s (it :: rest) = takeBoundaries v (takeItem v s it) rest := rfl
    rw [hstep]
    obtain ⟨hk, hm, hg, hb⟩ := ih (takeItem v s it)
    have h1 : (takeItem v s it).isRelative = s.isRelative ∧ (takeItem v s it).raw.map = s.raw.map ∧
        (takeItem v s it).raw.group = s.raw.group ∧
        ∀ (x : Digest) (a : Aci), (takeItem v s it).boundary[x]? = some a →
          s.boundary[x]? = some a ∨ (a = v ∧ ViewItem.boundary x ∈ it :: rest) := by
      cases it with
      | boundary d =>
        obtain ⟨k, m, g, b⟩ := takeBoundary_spec v s d
        refine ⟨k, m, g, fun x a h => ?_⟩
        rcases b x a h with h | ⟨rfl, rfl⟩
        · exact .inl h
        · exact .inr ⟨rfl, List.mem_cons_self⟩
      | record r aud => exact ⟨rfl, rfl, rfl, fun _ _ h => .inl h⟩
      | refused c => exact ⟨rfl, rfl, rfl, fun _ _ h => .inl h⟩
    obtain ⟨k1, m1, g1, b1⟩ := h1
    refine ⟨hk.trans k1, hm.trans m1, hg.trans g1, fun x a h => ?_⟩
    rcases hb x a h with h | ⟨rfl, hx⟩
    · exact b1 x a h
    · exact .inr ⟨rfl, List.mem_cons_of_mem _ hx⟩

/-- An item's record is in the batch `viewAccepted` accepts exactly when some item asks for it. -/
theorem mem_viewBatch {items : List ViewItem} {x : Rec} :
    x ∈ (items.filterMap ViewItem.record?).toArray ↔ ∃ aud, ViewItem.record x aud ∈ items := by
  simp only [List.mem_toArray, List.mem_filterMap]
  constructor
  · rintro ⟨it, hit, hx⟩
    cases it with
    | record r aud =>
      simp only [ViewItem.record?, Option.some.injEq] at hx
      subst hx
      exact ⟨aud, hit⟩
    | boundary _ => simp [ViewItem.record?] at hx
    | refused _ => simp [ViewItem.record?] at hx
  · rintro ⟨aud, h⟩
    exact ⟨_, h, rfl⟩

/-- **What `viewAccepted` does.** The kind and the chat are the same; every stored record is kept;
every new record is an item's; every new boundary digest is a boundary item's, vouched by `v`; and
`accept` on the result says `accepted` for an item's record only if it is stored there. -/
theorem viewAccepted_spec (s : ChatStore) (v : Aci) (items : List ViewItem) :
    (viewAccepted s v items).isRelative = s.isRelative ∧
    (viewAccepted s v items).raw.group = s.raw.group ∧
    (∀ (k : Digest) (x : Rec), s.get k = some x → (viewAccepted s v items).get k = some x) ∧
    (∀ (k : Digest) (x : Rec), (viewAccepted s v items).get k = some x →
      s.get k = some x ∨ ∃ aud, ViewItem.record x aud ∈ items) ∧
    (∀ (x : Digest) (a : Aci), (viewAccepted s v items).boundary[x]? = some a →
      s.boundary[x]? = some a ∨ (a = v ∧ ViewItem.boundary x ∈ items)) ∧
    (∀ r aud, ViewItem.record r aud ∈ items → ∀ d,
      ((viewAccepted s v items).accept r).1 = .accepted d →
        (viewAccepted s v items).get d = some r) := by
  let s1 := takeBoundaries v s items
  obtain ⟨k1, m1, g1, b1⟩ := takeBoundaries_spec v s items
  obtain ⟨k2, g2, b2, keep2, only2, acc2⟩ :=
    ChatStore.acceptAll_sound s1 (items.filterMap ViewItem.record?).toArray
  have hget1 : ∀ k, s1.get k = s.get k := fun k => by simp only [ChatStore.get, s1, m1]
  refine ⟨k2.trans k1, g2.trans g1, fun k x h => keep2 k x (by rw [hget1]; exact h),
    fun k x h => ?_, fun x a h => ?_, fun r aud hr d hd => acc2 r (mem_viewBatch.mpr ⟨aud, hr⟩) d hd⟩
  · rcases only2 k x h with h' | h'
    · exact .inl (by rw [← hget1]; exact h')
    · exact .inr (mem_viewBatch.mp h')
  · have h' : s1.boundary[x]? = some a := by
      have : (viewAccepted s v items).boundary = s1.boundary := b2
      rw [← this]; exact h
    exact b1 x a h'

/-- **What `viewStore` keeps of `viewAccepted`**: the kind, the records and the chat; its boundary
is part of `viewAccepted`'s. -/
theorem viewStore_spec (s : ChatStore) (v : Aci) (pd : Bool) (items : List ViewItem) :
    (viewStore s v pd items).isRelative = (viewAccepted s v items).isRelative ∧
    (viewStore s v pd items).raw.map = (viewAccepted s v items).raw.map ∧
    (viewStore s v pd items).raw.group = (viewAccepted s v items).raw.group ∧
    (∀ (x : Digest) (a : Aci), (viewStore s v pd items).boundary[x]? = some a →
      (viewAccepted s v items).boundary[x]? = some a) := by
  unfold viewStore
  split
  · obtain ⟨k, m, g, b, -⟩ := (viewAccepted s v items).prune_spec s.boundary
    exact ⟨k, m, g, b⟩
  · exact ⟨rfl, rfl, rfl, fun _ _ h => h⟩

/-- `accept` on `viewStore` says `accepted` for an item's record only if it is stored there. -/
theorem viewStore_accepted {s : ChatStore} {v : Aci} {pd : Bool} {items : List ViewItem}
    {r : Rec} {aud : Option (Array Serve.Seat)} (hr : ViewItem.record r aud ∈ items) {d : Digest}
    (h : ((viewStore s v pd items).accept r).1 = .accepted d) :
    (viewStore s v pd items).get d = some r := by
  obtain ⟨-, hm, hg, hb⟩ := viewStore_spec s v pd items
  obtain ⟨-, -, -, -, -, hacc⟩ := viewAccepted_spec s v items
  have hB : ∀ x ∈ (viewStore s v pd items).boundary, x ∈ (viewAccepted s v items).boundary := by
    intro x hx
    obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp (Std.ExtTreeMap.mem_iff_isSome_getElem?.mp hx)
    exact Std.ExtTreeMap.mem_iff_isSome_getElem?.mpr (by simp [hb x a ha])
  have := hacc r aud hr d (ChatStore.accept_fst_mono hm hg hB h)
  simp only [ChatStore.get] at this ⊢
  rw [hm]
  exact this

/-- `ACCEPT_VIEW`'s store is `viewStore` of the entries' items. -/
theorem acceptView_store (ch : Chat) (v : Aci) (imp pd : Bool) (es : Array ViewEntry) :
    (acceptView ch v imp pd es).2.store = viewStore ch.store v pd (es.toList.map (checkEntry imp)) :=
  rfl

/-- **What `ACCEPT_VIEW` does to a chat's store** (`acceptView_built` is by construction: the
store is a `ChatStore`, correct relative to its boundary, `ChatStore.builtRel`). The kind and the
chat are the same, so **a closed store stays closed and takes no boundary digest**. Every stored
record is kept. Every new record is the record of an entry that passed its checks. Every new
boundary digest is a boundary entry's, vouched by `v`. -/
theorem acceptView_sound (ch : Chat) (v : Aci) (imp pd : Bool) (es : Array ViewEntry) :
    (acceptView ch v imp pd es).2.store.isRelative = ch.store.isRelative ∧
    (acceptView ch v imp pd es).2.store.group = ch.store.group ∧
    (∀ (k : Digest) (x : Rec), ch.store.get k = some x →
      (acceptView ch v imp pd es).2.store.get k = some x) ∧
    (∀ (k : Digest) (x : Rec), (acceptView ch v imp pd es).2.store.get k = some x →
      ch.store.get k = some x ∨ ∃ e ∈ es, ∃ aud, checkEntry imp e = .record x aud) ∧
    (∀ (x : Digest) (a : Aci), (acceptView ch v imp pd es).2.store.boundary[x]? = some a →
      ch.store.boundary[x]? = some a ∨ (a = v ∧ ViewEntry.boundary x ∈ es)) := by
  rw [acceptView_store]
  let items := es.toList.map (checkEntry imp)
  obtain ⟨k3, m3, g3, b3⟩ := viewStore_spec ch.store v pd items
  obtain ⟨k2, g2, keep2, only2, b2, -⟩ := viewAccepted_spec ch.store v items
  have hget : ∀ k, (viewStore ch.store v pd items).get k = (viewAccepted ch.store v items).get k :=
    fun k => by simp only [ChatStore.get, m3]
  refine ⟨k3.trans k2, g3.trans g2, fun k x h => by rw [hget]; exact keep2 k x h,
    fun k x h => ?_, fun x a h => ?_⟩
  · rw [hget] at h
    rcases only2 k x h with h' | ⟨aud, h'⟩
    · exact .inl h'
    · obtain ⟨e, he, hce⟩ := List.mem_map.mp h'
      exact .inr ⟨e, Array.mem_toList_iff.mp he, aud, hce⟩
  · rcases b2 x a (b3 x a h) with h' | ⟨rfl, hx⟩
    · exact .inl h'
    · obtain ⟨e, he, hce⟩ := List.mem_map.mp hx
      exact .inr ⟨rfl, by rw [← checkEntry_boundary hce]; exact Array.mem_toList_iff.mp he⟩

/-- **`ACCEPT_VIEW` keeps the store correct relative to its boundary** (`BuiltRel`; for a closed
store the boundary is empty and this is `Built`). It holds by construction: the store is a
`ChatStore`, which carries the proof. -/
theorem acceptView_built (ch : Chat) (v : Aci) (imp pd : Bool) (es : Array ViewEntry) :
    BuiltRel (acceptView ch v imp pd es).2.store.raw (acceptView ch v imp pd es).2.store.boundary :=
  ChatStore.builtRel _

/-- **In per-digest mode, every boundary digest `ACCEPT_VIEW` adds is linked by a stored record**
(or is itself stored, a promotion): a digest answered by a per-digest reply is kept only if a
record of the store links it, one stored before or one accepted in the same request (a pending
record the host passes with the reply, docs/JOIN_PLAN.md §4.4). -/
theorem acceptView_boundary_linked (ch : Chat) (v : Aci) (imp : Bool) (es : Array ViewEntry)
    {x : Digest} (hx : x ∈ (acceptView ch v imp true es).2.store.boundary)
    (hnew : x ∉ ch.store.boundary) :
    x ∈ (acceptView ch v imp true es).2.store.raw.map ∨
      ∃ (k : Digest) (r : Rec), (acceptView ch v imp true es).2.store.get k = some r ∧
        x ∈ r.links := by
  rw [acceptView_store] at hx ⊢
  let items := es.toList.map (checkEntry imp)
  have hst : viewStore ch.store v true items = (viewAccepted ch.store v items).prune ch.store.boundary :=
    rfl
  obtain ⟨-, hm, -, -, hk⟩ := (viewAccepted ch.store v items).prune_spec ch.store.boundary
  rw [hst] at hx ⊢
  rcases hk x hx with h | h | ⟨k, r, hkr, hl⟩
  · exact absurd h hnew
  · exact .inl (by rw [hm]; exact h)
  · exact .inr ⟨k, r, by simp only [ChatStore.get, hm]; exact hkr, hl⟩

/-- **A per-digest `ACCEPT_VIEW` adds no head that is not a stored record.** Every head of the
store after it is a stored record or was a head before: a boundary digest a per-digest reply
carries never becomes a new head (the stray head of the round-2 review: a digest asked for by
name that no record of the requester links). -/
theorem acceptView_heads (ch : Chat) (v : Aci) (imp : Bool) (es : Array ViewEntry) {d : Digest}
    (hd : d ∈ (acceptView ch v imp true es).2.store.raw.heads) :
    d ∈ (acceptView ch v imp true es).2.store.raw.map ∨ d ∈ ch.store.raw.heads := by
  have hb := (acceptView ch v imp true es).2.store.builtRel
  obtain ⟨hmb, hnl⟩ := (hb.heads_iff d).mp hd
  rcases hmb with hm | hbd
  · exact .inl hm
  by_cases hold : d ∈ ch.store.boundary
  · refine .inr ((ch.store.builtRel.heads_iff d).mpr ⟨.inr hold, fun k x hk => ?_⟩)
    obtain ⟨-, -, keep, -, -⟩ := acceptView_sound ch v imp true es
    exact hnl k x (keep k x hk)
  · rcases acceptView_boundary_linked ch v imp es hbd hold with h | ⟨k, r, hkr, hl⟩
    · exact .inl h
    · exact absurd hl (hnl k r hkr)

/-- **`ACCEPT_VIEW` says `OK` for a record only if it is stored.** If the result for entry `i` is
`accepted d`, the entry is a record entry that passed its checks, `d` is that record's digest, and
the chat's store holds it under `d`. -/
theorem acceptView_accepted {ch : Chat} {v : Aci} {imp pd : Bool} {es : Array ViewEntry} {i : Nat}
    {d : Digest} (h : (acceptView ch v imp pd es).1[i]? = some (.record (.accepted d))) :
    ∃ e r aud, es[i]? = some e ∧ checkEntry imp e = .record r aud ∧ d = hashRecord r ∧
      (acceptView ch v imp pd es).2.store.get d = some r := by
  unfold acceptView at h
  simp only [List.getElem?_toArray, List.getElem?_map, Array.getElem?_toList] at h
  cases he : es[i]? with
  | none => simp [he] at h
  | some e =>
    rw [he] at h
    simp only [Option.map_some, Option.some.injEq] at h
    cases hce : checkEntry imp e with
    | record r aud =>
      rw [hce] at h
      simp only [ViewResult.record.injEq] at h
      have hr : ViewItem.record r aud ∈ es.toList.map (checkEntry imp) :=
        List.mem_map.mpr ⟨e, Array.mem_toList_iff.mpr (Array.mem_of_getElem? he), hce⟩
      exact ⟨e, r, aud, rfl, hce, (ChatStore.accept_accepted h).1, viewStore_accepted hr h⟩
    | boundary d' =>
      rw [hce] at h
      simp only at h
      split at h
      · simp at h
      · split at h <;> simp at h
    | refused c => rw [hce] at h; simp at h

/-- The audiences `acceptView`'s fold records come from record items whose record is stored. -/
theorem foldAudiences {s : ChatStore} (l : List ViewItem) (auds : AudTable) {d : Digest}
    {a : Array Serve.Seat}
    (h : (l.foldl (init := auds) fun auds it =>
      match it with
      | .record r (some a) => recordAudience auds (s.accept r).1 (some a)
      | _ => auds)[d]? = some a) :
    auds[d]? = some a ∨ ∃ r, ViewItem.record r (some a) ∈ l ∧ (s.accept r).1 = .accepted d := by
  induction l generalizing auds with
  | nil => exact .inl h
  | cons it rest ih =>
    simp only [List.foldl_cons] at h
    rcases ih _ h with h' | ⟨r, hr, hacc⟩
    · cases it with
      | record r0 aud =>
        cases aud with
        | none => exact .inl h'
        | some a0 =>
          cases hres : (s.accept r0).1 with
          | accepted d0 =>
            simp only [hres, recordAudience] at h'
            rw [Std.ExtTreeMap.getElem?_insert] at h'
            split at h'
            · rename_i hdd
              rw [Std.LawfulEqCmp.compare_eq_iff_eq] at hdd
              subst hdd
              cases h'
              exact .inr ⟨r0, List.mem_cons_self, hres⟩
            · exact .inl h'
          | _ => simp only [hres, recordAudience] at h'; exact .inl h'
      | boundary _ => exact .inl h'
      | refused _ => exact .inl h'
    · exact .inr ⟨r, List.mem_cons_of_mem _ hr, hacc⟩

/-- **`ACCEPT_VIEW` records only checked audiences of stored records.** An audience in the chat's
table after `ACCEPT_VIEW` was there before, or it is the audience of an entry's opening that
matches the entry's record (`checkEntry_record`), and that record is stored under `d`. -/
theorem acceptView_audiences {ch : Chat} {v : Aci} {imp pd : Bool} {es : Array ViewEntry}
    {d : Digest} {a : Array Serve.Seat} (h : (acceptView ch v imp pd es).2.audiences[d]? = some a) :
    ch.audiences[d]? = some a ∨ ∃ e ∈ es, ∃ r, checkEntry imp e = .record r (some a) ∧
      d = hashRecord r ∧ (acceptView ch v imp pd es).2.store.get d = some r := by
  unfold acceptView at h
  rcases foldAudiences _ _ h with h' | ⟨r, hr, hacc'⟩
  · exact .inl h'
  · right
    obtain ⟨e, he, hce⟩ := List.mem_map.mp hr
    exact ⟨e, Array.mem_toList_iff.mp he, r, hce, (ChatStore.accept_accepted hacc').1,
      viewStore_accepted hr hacc'⟩

/-- `ACCEPT_VIEW` runs `acceptView` on the chat, with the reply's entries and then the pending
ones, and puts the result back. -/
theorem run_acceptView {build : String} {t t' : Table} {chat : String} {v : Aci} {imp pd : Bool}
    {es ps : Array ViewEntry} {rs : Array ViewResult}
    (h : run build t (.acceptView chat v imp pd es ps) = (.viewed rs, t')) :
    ∃ ch, t[chat]? = some ch ∧ rs = (acceptView ch v imp pd (es ++ ps)).1 ∧
      t'[chat]? = some (acceptView ch v imp pd (es ++ ps)).2 := by
  simp only [run, takeOut] at h
  cases hch : t[chat]? with
  | none => simp [hch] at h
  | some ch =>
    simp only [hch, Prod.mk.injEq, Reply.viewed.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨ch, rfl, rfl, Std.HashMap.getElem?_insert_self⟩

/-- **A per-digest `ACCEPT_VIEW` request adds no head that is not a stored record**
(`acceptView_heads`, on the table): whatever the reply's boundary entries, every head of the chat
after it is a stored record or was a head before. So the requester's heads, its compare code, stay
those of the records it holds and of the catch-up that created the store. -/
theorem run_acceptView_heads {build : String} {t t' : Table} {chat : String} {v : Aci}
    {imp : Bool} {es ps : Array ViewEntry} {rs : Array ViewResult}
    (h : run build t (.acceptView chat v imp true es ps) = (.viewed rs, t')) :
    ∃ ch ch', t[chat]? = some ch ∧ t'[chat]? = some ch' ∧
      ∀ d ∈ ch'.store.raw.heads, d ∈ ch'.store.raw.map ∨ d ∈ ch.store.raw.heads := by
  obtain ⟨ch, hch, -, ht'⟩ := run_acceptView h
  exact ⟨ch, _, hch, ht', fun d hd => acceptView_heads ch v imp (es ++ ps) hd⟩

/-- A digest is in the set built from a list exactly when it is in the list. -/
theorem mem_foldl_insert {l : List Digest} {s : DigestSet} {d : Digest} :
    d ∈ l.foldl (·.insert ·) s ↔ d ∈ s ∨ d ∈ l := by
  induction l generalizing s with
  | nil => simp
  | cons x xs ih =>
    rw [List.foldl_cons, ih, Std.ExtTreeSet.mem_insert, Std.LawfulEqCmp.compare_eq_iff_eq,
      List.mem_cons]
    constructor
    · rintro ((rfl | h) | h)
      · exact .inr (.inl rfl)
      · exact .inl h
      · exact .inr (.inr h)
    · rintro (h | rfl | h)
      · exact .inl (.inr h)
      · exact .inl (.inl rfl)
      · exact .inr h

/-- **`LINKABLE` returns only heads, and for a relative store only live records.** Every digest it
returns is a head of the chat's store (no stored record links it); for a relative store it is
also a stored record and in the `live` list the host passed (docs/JOIN_PLAN.md §6.2). Nothing
changes. -/
theorem run_linkable {build : String} {t t' : Table} {chat : String} {live : Array Digest}
    {ds : Array Digest} (h : run build t (.linkable chat live) = (.digests ds, t')) :
    t' = t ∧ ∃ ch, t[chat]? = some ch ∧ ∀ d ∈ ds,
      (∀ (k : Digest) (x : Rec), ch.store.get k = some x → d ∉ x.links) ∧
      (ch.store.isRelative = true → (∃ r, ch.store.get d = some r) ∧ d ∈ live) := by
  simp only [run, reading] at h
  split at h
  · rename_i ch hch
    simp only [Prod.mk.injEq, Reply.digests.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨rfl, ch, hch, fun d hd => ?_⟩
    obtain ⟨hn, hr⟩ := ChatStore.linkable_sub hd
    refine ⟨hn, fun hrel => ?_⟩
    obtain ⟨h1, h2⟩ := hr hrel
    refine ⟨h1, ?_⟩
    rw [← Array.foldl_toList, mem_foldl_insert] at h2
    rcases h2 with h2 | h2
    · simp at h2
    · exact Array.mem_toList_iff.mp h2
  · simp at h

/-- **`NEW_RELATIVE` opens an empty relative store**, and `NEW` an empty closed one. -/
theorem run_newRelative {build : String} {t t' : Table} {chat : String} {g : GroupId}
    (h : run build t (.newRelative chat g) = (.ok, t')) :
    ∃ ch, t'[chat]? = some ch ∧ ch.store.isRelative = true ∧ ch.store.group = g ∧
      ch.store.headsArray = #[] := by
  simp only [run] at h
  split at h
  · simp at h
  · simp only [Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    refine ⟨_, Std.HashMap.getElem?_insert_self, rfl, rfl, ?_⟩
    simp [ChatStore.headsArray, RelStore.headsArray, RelStore.heads, RelStore.empty,
      RelStore.emptyWith, keySet]

/-! ### The theorems on concrete inputs

A closed chat that holds `a1` takes a view whose one entry is `a1`'s record: the reply says
`accepted`, so the hypothesis of `acceptView_accepted` holds. `LINKABLE` and `NEW_RELATIVE` reply
as their theorems assume. -/

/-- A closed chat holding `a1` (`Zrdt.Examples.s1`). -/
def chatA1 : Chat := { store := .closed Examples.s1 }

/-- `a1` is stored in it. -/
theorem chatA1_get : chatA1.store.get (hashRecord Examples.a1) = some Examples.a1 := by
  have hok : (rawAccept (CheckedStore.empty Examples.group).raw Examples.a1).1 =
      .accepted (hashRecord Examples.a1) :=
    rawAccept_of_ok rfl (by decide) (by simp [Examples.a1]) (by simp [CheckedStore.empty])
      (fun _ => by simp [CheckedStore.empty, maxRecords])
  have h := rawAccept_accepted (c' := (rawAccept (CheckedStore.empty Examples.group).raw
    Examples.a1).2) (Prod.ext hok rfl)
  show (rawAccept (CheckedStore.empty Examples.group).raw Examples.a1).2.map[hashRecord
    Examples.a1]? = some Examples.a1
  rw [h.2.2.1]
  exact Std.ExtTreeMap.getElem?_insert_self

/-- The view's one result is `accepted`, in either mode. -/
theorem chatA1_view (pd : Bool) : (acceptView chatA1 Examples.alice false pd
    #[.after (encode Examples.a1)]).1[0]? = some (.record (.accepted (hashRecord Examples.a1))) := by
  have hce : checkEntry false (.after (encode Examples.a1)) = .record Examples.a1 none := by
    simp [checkEntry, decode_encode]
  have hst : (viewStore chatA1.store Examples.alice pd [.record Examples.a1 none]).get
      (hashRecord Examples.a1) = some Examples.a1 := by
    obtain ⟨-, hm, -, -⟩ := viewStore_spec chatA1.store Examples.alice pd [.record Examples.a1 none]
    obtain ⟨-, -, keep, -, -, -⟩ :=
      viewAccepted_spec chatA1.store Examples.alice [.record Examples.a1 none]
    have := keep _ _ chatA1_get
    simp only [ChatStore.get] at this ⊢
    rw [hm]
    exact this
  simp only [acceptView, List.map_cons, List.map_nil, hce, List.getElem?_toArray,
    List.getElem?_cons_zero, Option.some.injEq, ViewResult.record.injEq]
  exact ChatStore.accept_stored hst

example : ∃ e r aud, (#[ViewEntry.after (encode Examples.a1)])[0]? = some e ∧
    checkEntry false e = .record r aud ∧ hashRecord Examples.a1 = hashRecord r ∧
    (acceptView chatA1 Examples.alice false true #[.after (encode Examples.a1)]).2.store.get
      (hashRecord Examples.a1) = some r :=
  acceptView_accepted (chatA1_view true)

example : ∃ ds t', run buildId ((∅ : Table).insert "a" chatA1) (.linkable "a" #[]) =
    (.digests ds, t') :=
  ⟨_, _, by simp only [run, reading, Std.HashMap.getElem?_insert_self]; rfl⟩

example : ∃ ch, ((run buildId (∅ : Table) (.newRelative "n" Examples.group)).2)["n"]? = some ch ∧
    ch.store.isRelative = true ∧ ch.store.group = Examples.group ∧ ch.store.headsArray = #[] :=
  run_newRelative (build := buildId) (t := ∅) (by simp [run])

/-! ### `run_serve_content` on a real request

A table holding Alice's message to herself (`Serve.Examples.selfMsg`), and her own `SERVE`
request for her account: the reply holds the message with its opening, as an author copy. So the
hypothesis of `run_serve_content` is met, and its content clause is not vacuous. -/

open Serve.Examples in
/-- Chat `"self"`: Alice's message to herself, no audience recorded. -/
def selfTable : Table := (∅ : Table).insert "self" { store := .closed selfStore }

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
    Serve.serve selfStore.raw selfServe.me (selfServe.heldMap ∅) selfServe.query, selfTable, ?_, ?_⟩
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
-- Open a chat, accept `a1` and then `b1` (structure only), read the heads, close.
#guard session [(Request.new "c" group).write, (Request.acceptRecord "c" (encode a1) none).write,
    (Request.acceptRecord "c" (encode b1) none).write, (Request.heads "c").write,
    (Request.close "c").write,
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
