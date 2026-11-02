import Zrdt.Proto
import Zrdt.Apps

/-!
# Test vectors (docs/PLAN.md §4 C, rungs 6 and 7)

`Zrdtd/Vectors.lean` prints `vectors/vectors.json` from this file (`make vectors`). The host's
TypeScript stub and `zrdtd` are both run over it and must give these bytes. This file has no
`main`, so the library `Zrdt` imports it and a plain `lake build` runs the `#guard`s below.

The file holds:

- `sha256`: the NIST examples (FIPS 180-4) and inputs around the padding boundaries;
- `records`: records as the host gives them (`linksGiven`, any order, repeats allowed), their
  canonical links, their encoding and their digest;
- `recordDecode`, `blobDecode`: bytes, and whether the strict decoders accept them (for blobs,
  also whether the count field alone makes them `TOO_LARGE`);
- `blobs`: `zrdtS2` records blobs (the last part of a `zrdtS3` store blob, `Zrdt.ChatStore`);
- `commit`: `DataMessage` bytes, the bytes the commitment covers, the commitment and the opening
  (`null` where the message is malformed), including messages with fields 15 and 200, and the
  audience each opening carries (`null` where it has none: `ACCEPT` refuses such an opening);
- `keyTag`: identity keys (33 bytes) and their tags (`Serve.keyTag`), which the host checks
  before it seals a `SERVE` reply (docs/JOIN_PLAN.md §4.3);
- `replies`: reply bytes that no request can produce here (`COLLISION` needs two records with the
  same SHA-256);
- `sessions`: request and reply payloads. Run each session on a fresh `zrdtd`, in order: send
  `length (u32) ‖ request`, read `length (u32) ‖ reply`, and compare the reply. Every op and every
  reply of every op appears, except `COLLISION`. The `view` session is a newcomer's relative
  store (`NEW_RELATIVE`, `ACCEPT_VIEW` of a `SERVE` reply's entries byte for byte, `LINKABLE`,
  its `zrdtS3` blob), a second-generation newcomer, and a closed store that ignores boundary
  entries. The `fuzz` session holds unreadable requests and
  counts no input could hold. A step marked `buildDependent` (`VERSION`) contains the build text:
  another build of `zrdtd` gives other bytes there. The file's `build` is the text of the
  `zrdtd` built from the same sources.

Each step states the status it must get; the `#guard`s below check them, and pin some reply
bodies, when this file is built.

**Protocol 5** (docs/apps/BUILD_M1.md). Every session runs through `Zrdt.Apps.session`, the
dispatcher `zrdtd` runs; on protocol-4 requests it gives protocol 4's replies. Each lane owns two
sections of this file, marked `[BEGIN lane <x>]` and `[END lane <x>]`: its sessions (before
`sessions`) and its checks (after). A lane edits only its own sections; `sessions` already lists
`baseSessions`, `torrentSessions` and `gitSessions`.
-/

namespace Zrdt.Vectors

open Proto Examples
open Serve.Examples (keyAlice keyBob keyCarol keyMallory keyBob' mallory audienceFieldOf
  audienceOfKeys pre welcome stale later timed noAudience AC ABC)

/-! ## A small JSON writer -/

/-- A JSON value. -/
inductive Json
  | null
  | bool (b : Bool)
  | num (n : Nat)
  | str (s : String)
  | arr (xs : Array Json)
  | obj (kvs : Array (String × Json))
deriving Inhabited

/-- `s` as a JSON string, with `"`, `\` and control characters escaped. -/
def quote (s : String) : String :=
  let body := s.foldl (init := "") fun acc c =>
    if c == '"' then acc ++ "\\\"" else if c == '\\' then acc ++ "\\\\"
    else if c.toNat < 0x20 then acc ++ "\\u00" ++ hexOfBytes ⟨#[c.toNat.toUInt8]⟩
    else acc.push c
  "\"" ++ body ++ "\""

#guard quote "a\"b\\c\n" == "\"a\\\"b\\\\c\\u000a\""

/-- Whether a value is printed on one line: everything but arrays and objects that hold arrays
or objects of arrays or objects. -/
def Json.flat : Json → Bool
  | .arr xs => xs.all fun x => match x with | .arr _ | .obj _ => false | _ => true
  | .obj kvs => kvs.all fun (_, v) => match v with
    | .arr xs => xs.all fun x => match x with | .arr _ | .obj _ => false | _ => true
    | .obj _ => false
    | _ => true
  | _ => true

/-- The JSON text of a value; nested values are indented by `pad`. -/
partial def Json.render (pad : String) : Json → String
  | .null => "null"
  | .bool b => if b then "true" else "false"
  | .num n => toString n
  | .str s => quote s
  | j@(.arr xs) =>
    if j.flat then "[" ++ ", ".intercalate (xs.map (·.render pad)).toList ++ "]"
    else
      let inner := pad ++ "  "
      "[\n" ++ ",\n".intercalate (xs.map fun x => inner ++ x.render inner).toList ++ "\n" ++
        pad ++ "]"
  | j@(.obj kvs) =>
    if j.flat then
      "{" ++ ", ".intercalate (kvs.map fun (k, v) => quote k ++ ": " ++ v.render pad).toList ++ "}"
    else
      let inner := pad ++ "  "
      "{\n" ++ ",\n".intercalate (kvs.map fun (k, v) => inner ++ quote k ++ ": " ++
        v.render inner).toList ++ "\n" ++ pad ++ "}"

#guard (Json.obj #[("a", .arr #[.num 1, .null])]).render "" == "{\"a\": [1, null]}"

/-- Bytes as a JSON hex string. -/
def hex (b : ByteArray) : Json := .str (hexOfBytes b)

/-- Digests as a JSON array of hex strings. -/
def hexes (ds : Array Digest) : Json := .arr (ds.map (hex ·.bytes))

/-! ## SHA-256 -/

/-- The NIST examples and inputs around the padding boundaries (also checked in `Zrdt.Sha256`). -/
def shaInputs : Array (String × ByteArray) :=
  #[("empty", .empty), ("abc", "abc".toUTF8),
    ("448 bits", "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq".toUTF8),
    ("896 bits", ("abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghijklmnhijklmno" ++
      "ijklmnopjklmnopqklmnopqrlmnopqrsmnopqrstnopqrstu").toUTF8)] ++
  #[55, 56, 63, 64, 65, 119, 120].map fun n => (s!"boundary {n}", boundaryMsg n)

/-- The `sha256` section. The million-`a` example is given as a byte and a count. -/
def shaJson : Json :=
  .arr <| shaInputs.map (fun (name, m) =>
    .obj #[("name", .str name), ("input", hex m), ("digest", hex (sha256 m).bytes)]) |>.push
    (.obj #[("name", .str "one million a"), ("repeatByte", .str "61"), ("count", .num 1000000),
      ("digest", .str "cdc76e5c9914fb9281a1c7e284d73e67f1809a48a497200e046d39ccc7112cd0")])

/-! ## Records and blobs -/

/-- A record that a member writes in parallel with a different chat: same parts, other group. -/
def foreign : Rec := Rec.make otherGroup (dig 0xd1) #[] alice

/-- Example records as the host gives them: a name, and parts whose links may be unsorted. -/
def recordParts : Array (String × Parts) :=
  #[("first", .ofRec first), ("reply, links given as 03 01 03 02", ⟨group, dig 0xc1,
      #[dig 3, dig 1, dig 3, dig 2], alice⟩),
    ("a1", .ofRec a1), ("b1", .ofRec b1), ("c1", .ofRec c1), ("a2", .ofRec a2),
    ("f1", .ofRec f1), ("a3", .ofRec a3), ("b2", .ofRec b2), ("c2", .ofRec c2),
    ("foreign (other group)", .ofRec foreign)]

/-- The `records` section. -/
def recordsJson : Json :=
  .arr <| recordParts.map fun (name, p) =>
    let r := p.toRec
    .obj #[("name", .str name), ("group", hex p.group.bytes), ("commit", hex p.commit.bytes),
      ("linksGiven", hexes p.links), ("links", hexes r.links), ("author", hex p.author.bytes),
      ("encoding", hex (encode r)), ("digest", hex (hashRecord r).bytes)]

/-- Record bytes, and whether `decode` accepts them (from the examples in `Zrdt.Encode`). -/
def recordDecodeCases : Array (String × ByteArray) :=
  #[("first", encode first), ("reply", encode reply), ("empty", .empty),
    ("first with a byte too many", (encode first).push 0),
    ("reply with a byte too few", (encode reply).extract 0 184),
    ("first with a wrong tag", (encode first).set! 0 0x5a),
    ("reply with nlinks 2 for 3 links", (encode reply).set! 72 2),
    ("reply with 4 links and nlinks 3", encode reply ++ (encode reply).extract 73 105),
    ("two links out of order", (bytesOfHex? (twoLinksHex "02" "01")).getD .empty),
    ("two equal links", (bytesOfHex? (twoLinksHex "01" "01")).getD .empty),
    ("two links in order", (bytesOfHex? (twoLinksHex "01" "02")).getD .empty)]

/-- The `recordDecode` section. -/
def recordDecodeJson : Json :=
  .arr <| recordDecodeCases.map fun (name, b) =>
    .obj #[("name", .str name), ("bytes", hex b), ("decodes", .bool (decode b).isSome)]

/-- Example blobs: a name, the group, and the records in the order written. -/
def blobCases : Array (String × GroupId × Array Rec) :=
  #[("first and reply", group, #[first, reply]), ("a1 b1 c1 a2 (all4)", group, all4.records),
    ("empty, other group", otherGroup, #[]),
    ("doctored: all4 without b1", group, #[a1, c1, a2])]

/-- The `blobs` section. -/
def blobsJson : Json :=
  .arr <| blobCases.map fun (name, g, rs) =>
    .obj #[("name", .str name), ("group", hex g.bytes),
      ("records", .arr (rs.map (hex <| encode ·))),
      ("blob", hex (encodeBlob g rs))]

/-- A blob header that claims 2^32 - 1 records, with nothing after it. -/
def hugeCountBlob : ByteArray := blobTag ++ group.bytes ++ ⟨#[0xff, 0xff, 0xff, 0xff]⟩

/-- Blob bytes, and whether `decodeBlob` accepts them. -/
def blobDecodeCases : Array (String × ByteArray) :=
  #[("first", encodeBlob group #[first]),
    ("a byte left over", (encodeBlob group #[first]).push 0),
    ("count says 2", (encodeBlob group #[first]).set! 41 2),
    ("len says 90", (encodeBlob group #[first]).set! 45 90),
    ("wrong tag", (encodeBlob group #[first]).set! 0 0),
    ("records out of digest order", encodeBlob group #[reply, first]),
    ("a record twice", encodeBlob group #[first, first]),
    ("fuzz: count 2^32 - 1 and nothing after it", hugeCountBlob),
    ("count 2^24 and nothing after it: too large", blobTag ++ group.bytes ++ u32be (2^24)),
    ("count 2^24 - 1 and nothing after it: not too large, malformed",
      blobTag ++ group.bytes ++ u32be (2^24 - 1))]

/-- The `blobDecode` section. `tooLarge`: the count field alone makes the blob `TOO_LARGE`
(`blobTooLarge`); such a blob never decodes. -/
def blobDecodeJson : Json :=
  .arr <| blobDecodeCases.map fun (name, b) =>
    .obj #[("name", .str name), ("bytes", hex b), ("decodes", .bool (decodeBlob b).isSome),
      ("tooLarge", .bool (blobTooLarge b))]

#guard (blobDecodeCases.map fun (_, b) => ((decodeBlob b).isSome, blobTooLarge b)) ==
  #[(true, false), (false, false), (false, false), (false, false), (false, false),
    (true, false), (true, false), (false, true), (false, true), (false, false)]

/-! ## Commitments -/

/-- `dataMessage` with an audience (field 201): Alice and Bob under their keys. -/
def m1Message : ByteArray :=
  dataMessage ++ audienceFieldOf [(alice, some keyAlice), (bob, some keyBob)]

/-- Example `DataMessage` bytes (fields from `Zrdt.Commit`'s examples). -/
def commitCases : Array (String × ByteArray) :=
  #[("body, groupV2 (15), timestamp, zrdt (200), unknown field 99", dataMessage),
    ("the same without fields 15 and 200 (the opening)",
      bodyField ++ timestampField ++ unknownField),
    ("empty", .empty),
    ("field 15 twice, around the body", groupV2Field ++ bodyField ++ groupV2Field),
    ("field 15 with a longer form of its key (fa 00)", bytesOf [0xfa, 0x00, 0] ++ bodyField),
    ("field 200 only", zrdtField),
    ("the message with an audience (201): alice and bob under their keys", m1Message),
    ("an audience given twice", m1Message ++ audienceFieldOf [(alice, some keyAlice)]),
    ("an audience whose entries are out of order",
      dataMessage ++ audienceFieldOf [(bob, some keyBob), (alice, some keyAlice)]),
    ("malformed: cut short", dataMessage.extract 0 (dataMessage.size - 1)),
    ("malformed: wire type 3 (a group)", bodyField ++ bytesOf [0x0b]),
    ("malformed: field number 0", bytesOf [0x02, 0x00]),
    ("malformed: an 11-byte varint", bytesOf ([0x08] ++ List.replicate 10 0xff ++ [0x01])),
    ("malformed: a length past the end", bytesOf [0x0a, 0xff, 0xff, 0xff, 0xff, 0x0f, 0x41])]

/-- The `commit` section: group `67…`, author `a1…` (alice), nonce `4e…`. -/
def commitJson : Json :=
  .arr <| commitCases.map fun (name, m) =>
    .obj #[("name", .str name), ("group", hex group.bytes), ("author", hex alice.bytes),
      ("nonce", hex nonce.bytes), ("dataMessage", hex m),
      ("committedBytes", ((committedBytes m).map hex).getD .null),
      ("commit", ((commit group alice nonce m).map (hex ·.bytes)).getD .null),
      ("opening", ((commitWithOpening group alice nonce m).map (hex ·.2)).getD .null),
      ("audience", (((commitWithOpening group alice nonce m).bind
        (Serve.audienceOf ·.2)).map (hex <| Serve.writeAudience ·)).getD .null)]

-- The opening has the same commitment as the full message; malformed messages have none.
#guard (commitCases.map fun (_, m) => (commit group alice nonce m).isSome) ==
  #[true, true, true, true, true, true, true, true, true, false, false, false, false, false]
-- Only the message with one well-formed field 201 has an audience.
#guard (commitCases.map fun (_, m) => ((commitWithOpening group alice nonce m).bind
  (Serve.audienceOf ·.2)).isSome) ==
  #[false, false, false, false, false, false, true, false, false, false, false, false, false, false]
#guard commit group alice nonce commitCases[0]!.2 == commit group alice nonce commitCases[1]!.2

/-! ## Key tags -/

/-- Identity keys: the example keys (33 bytes of one value) and a key shaped like libsignal's
(`05` then 32 bytes). -/
def keyTagCases : Array (String × ByteArray) :=
  #[("33 bytes 01 (keyAlice)", keyAlice), ("33 bytes 02 (keyBob)", keyBob),
    ("33 bytes 03 (keyCarol)", keyCarol),
    ("05 then 00 01 .. 1f", ⟨#[5] ++ (List.range 32).toArray.map (·.toUInt8)⟩)]

/-- The `keyTag` section. -/
def keyTagJson : Json :=
  .arr <| keyTagCases.map fun (name, k) =>
    .obj #[("name", .str name), ("key", hex k), ("tag", hex ⟨Serve.keyTag k⟩)]

-- Expected values from Python's `hashlib`: sha256(b"zrdtK1" + key)[:16].
#guard keyTagCases.map (hexOfBytes ⟨Serve.keyTag ·.2⟩) ==
  #["c91d28e8389a0f4aafe0c33da959495b", "08b1c55ca9baa489f107f92595cfb3a6",
    "ec03427ff7dc538d1442ebddc57df815", "d2533f208a5514a7cfc67bbe9fc20de4"]

/-! ## Request and reply sessions -/

/-- One request, the status its reply must have, and optionally the whole reply. -/
structure Step where
  /-- What the step does. -/
  name : String
  /-- The request payload. -/
  request : ByteArray
  /-- The status its reply must have. -/
  expect : Code
  /-- The whole reply payload, where a step pins it. -/
  reply? : Option ByteArray := none
  /-- The reply holds the build text (`VERSION`). -/
  buildDependent : Bool := false

/-- A step from a request. -/
def ask (name : String) (q : Request) (expect : Code) (reply? : Option Reply := none) : Step :=
  { name, request := q.write, expect, reply? := reply?.map (·.write) }

/-- A step from raw request bytes. -/
def raw (name : String) (b : ByteArray) (expect : Code) : Step := { name, request := b, expect }

/-- Digests, sorted. -/
def sorted (ds : Array Digest) : Array Digest := ds.qsort (compare · · == .lt)

/-- Alice's message `m1Message` (`dataMessage` with an audience): its commitment and its
opening. -/
def m1Opened : Digest × ByteArray :=
  (commitWithOpening group alice nonce m1Message).getD (Digest.zero, .empty)

/-- The `COMMIT` reply for `m1Message`. -/
def m1Committed : Reply := .committed m1Opened.1 m1Opened.2

/-- `dataMessage` (no audience): its commitment and its opening. -/
def m0Opened : Digest × ByteArray :=
  (commitWithOpening group alice nonce dataMessage).getD (Digest.zero, .empty)

/-- A record of Alice's whose commit is that of `dataMessage`, which has no audience. -/
def m0 : Rec := Rec.make group m0Opened.1 #[hashRecord a1] alice

/-- A record of Alice's whose commit is the real commitment of `dataMessage`. It links `a1`. -/
def m1 : Rec := Rec.make group m1Opened.1 #[hashRecord a1] alice

/-- The same commit and links in Bob's name: Alice's opening does not belong to it. -/
def m1AsBob : Rec := Rec.make group m1Opened.1 #[hashRecord a1] bob

/-- `m1Message` committed in another group: its commitment and its opening. -/
def m1ForeignOpened : Digest × ByteArray :=
  (commitWithOpening otherGroup alice nonce m1Message).getD (Digest.zero, .empty)

/-- A record of another group whose opening (`m1ForeignOpened`) matches it. -/
def m1Foreign : Rec := Rec.make otherGroup m1ForeignOpened.1 #[] alice

/-- `m1`'s commit with 4097 links: too large, though its opening matches. -/
def m1TooLarge : Rec := Rec.make group m1Opened.1 tooManyLinks.links alice

#guard openingMatches otherGroup alice m1Foreign.commit m1ForeignOpened.2 &&
  openingMatches group alice m1TooLarge.commit m1Opened.2 && !m1TooLarge.WellSized
#guard openingMatches group alice m1.commit m1Opened.2 && m1Opened.2.size == 32 + 20 + 67
#guard (Serve.audienceOf m1Opened.2).isSome && (Serve.audienceOf m0Opened.2).isNone

/-- The facts given to `CLASSIFY` in the tour: Alice's `a3` and Bob's `b2` live (Bob disowns
the fake `f1`), `c2` relayed by Bob, `f1` imported, and a live digest that is not stored. -/
def tourFacts : Array Fact :=
  #[liveFact a3, liveFact b2 #[hashRecord f1], ⟨hashRecord c2, .relayed bob, #[]⟩,
    ⟨hashRecord f1, .imported, #[]⟩, ⟨dig 9, .live, #[]⟩]

/-- The statuses `CLASSIFY` must give in the tour: all four kinds. -/
def tourStatuses : Array (Digest × Status) :=
  (#[(a1, Status.confirmedByAuthor), (b1, .confirmedByAuthor), (c1, .heldBy alice),
      (a2, .confirmedByAuthor), (f1, .notConfirmedByAuthor), (a3, .confirmedByAuthor),
      (b2, .confirmedByAuthor), (c2, .unconfirmed)].map fun (r, s) => (hashRecord r, s)).qsort
    fun x y => compare x.1 y.1 == .lt

/-- A closed `zrdtS3` blob around a `zrdtS2` records blob: mode 0, no boundary, no audiences. -/
def s3 (inner : ByteArray) : ByteArray := blob3Tag ++ ⟨#[0]⟩ ++ u32be 0 ++ u32be 0 ++ inner

-- A closed store with no audiences is written exactly so.
#guard encodeChat (.closed all4) ∅ == s3 all4.encode

/-- A record list with one entry that does not decode (the first record with a byte too many). -/
def badList : Input := .records #[encode a1, (encode first).push 0]

/-- The main session: every op, and every reply of every op except `COLLISION` and the fuzz
cases. -/
def tour : Array Step := #[
  { ask "VERSION" .version .ok with buildDependent := true },
  ask "HEADS before any NEW: no chat" (.heads "camping") .noChat,
  ask "NEW camping" (.new "camping" group) .ok,
  ask "NEW camping again: already open" (.new "camping" group) .chatOpen,
  ask "HEADS of an empty store" (.heads "camping") .ok (some (.digests #[])),
  ask "HASH of first" (.hash (.ofRec first)) .ok (some (.digest (hashRecord first))),
  ask "HASH with links 03 01 03 02: sorted, repeat dropped (= reply)"
    (.hash ⟨group, dig 0xc1, #[dig 3, dig 1, dig 3, dig 2], alice⟩) .ok
    (some (.digest (hashRecord reply))),
  ask "ACCEPT_RECORD a1 (structure only): its digest and encoding"
    (.acceptRecord "camping" (encode a1) none) .ok (some (.accept a1 (.accepted (hashRecord a1)))),
  ask "ACCEPT_RECORD a1 again: accepted, nothing changes" (.acceptRecord "camping" (encode a1) none)
    .ok (some (.accept a1 (.accepted (hashRecord a1)))),
  ask "ACCEPT_RECORD a2 before b1 and c1: missing both, sorted"
    (.acceptRecord "camping" (encode a2) none)
    .missing (some (.accept a2 (.missing (sorted #[hashRecord b1, hashRecord c1])))),
  ask "HEADS: a1" (.heads "camping") .ok (some (.digests #[hashRecord a1])),
  ask "ACCEPT_RECORD b1" (.acceptRecord "camping" (encode b1) none) .ok,
  ask "ACCEPT_RECORD c1" (.acceptRecord "camping" (encode c1) none) .ok
    (some (.accept c1 (.accepted (hashRecord c1)))),
  ask "HEADS: b1 and c1, sorted" (.heads "camping") .ok
    (some (.digests (sorted #[hashRecord b1, hashRecord c1]))),
  ask "ACCEPT_RECORD a2" (.acceptRecord "camping" (encode a2) none) .ok,
  ask "ACCEPT_RECORD a record of another group: wrong chat"
    (.acceptRecord "camping" (encode foreign) none) .wrongChat,
  ask "HEADS: a2" (.heads "camping") .ok (some (.digests #[hashRecord a2])),
  ask "HAS a1" (.has "camping" (hashRecord a1)) .ok (some (.has true)),
  ask "HAS a digest that is not stored" (.has "camping" (dig 9)) .ok (some (.has false)),
  ask "GET b1" (.get "camping" (hashRecord b1)) .ok (some (.record b1)),
  ask "GET a digest that is not stored" (.get "camping" (dig 9)) .notFound,
  ask "REACH_SET from b1" (.reachSet "camping" #[hashRecord b1]) .ok
    (some (.digests (sorted #[hashRecord a1, hashRecord b1]))),
  ask "REACH_SET from a2 and a digest that is not stored" (.reachSet "camping"
    #[dig 9, hashRecord a2]) .ok
    (some (.digests (sorted #[hashRecord a1, hashRecord b1, hashRecord c1, hashRecord a2]))),
  ask "COMMIT a DataMessage with fields 15, 200 and 201: the commitment and the opening"
    (.commit group alice nonce m1Message) .ok (some m1Committed),
  ask "COMMIT the opening's bytes (fields 15 and 200 already removed): the same reply"
    (.commit group alice nonce (m1Opened.2.extract 32 m1Opened.2.size)) .ok
    (some m1Committed),
  ask "COMMIT a malformed DataMessage" (.commit group alice nonce (bodyField ++ bytesOf [0x0b]))
    .malformed,
  ask "ENCODE camping (a1 b1 c1 a2)" (.encode "camping") .ok (some (.blob (s3 all4.encode))),
  ask "ACCEPT_RECORD f1 (a fake in Bob's name)" (.acceptRecord "camping" (encode f1) none) .ok,
  ask "ACCEPT_RECORD a3" (.acceptRecord "camping" (encode a3) none) .ok,
  ask "ACCEPT_RECORD b2" (.acceptRecord "camping" (encode b2) none) .ok,
  ask "ACCEPT_RECORD c2" (.acceptRecord "camping" (encode c2) none) .ok,
  ask "CLASSIFY: a3, b2 live (b2 disowns f1), c2 relayed, f1 imported"
    (.classify "camping" tourFacts) .ok (some (.classified tourStatuses)),
  ask "CLASSIFY with no facts: all unconfirmed" (.classify "camping" #[]) .ok
    (some (.classified (tourStatuses.map fun (d, _) => (d, .unconfirmed)))),
  ask "OPEN copy from a blob" (.open "copy" group (.blob (s3 all4.encode))) .ok,
  ask "HEADS of copy: a2" (.heads "copy") .ok (some (.digests #[hashRecord a2])),
  ask "OPEN copy again: already open" (.open "copy" group (.blob (s3 all4.encode))) .chatOpen,
  ask "OPEN list from records in any order" (.open "list" group
    (.records #[encode a2, encode c1, encode b1, encode a1])) .ok,
  ask "ENCODE list: the same blob as camping had" (.encode "list") .ok
    (some (.blob (s3 all4.encode))),
  ask "OPEN rev from a blob with the records in reverse digest order" (.open "rev" group
    (.blob (s3 (encodeBlob group all4.records.reverse)))) .ok,
  ask "ENCODE rev: the records sorted by digest" (.encode "rev") .ok
    (some (.blob (s3 all4.encode))),
  ask "OPEN rep from a blob that holds b1 twice" (.open "rep" group
    (.blob (s3 (encodeBlob group #[a1, b1, c1, b1, a2])))) .ok,
  ask "ENCODE rep: b1 counts once" (.encode "rep") .ok (some (.blob (s3 all4.encode))),
  ask "OPEN rep2 from a record list that holds a1 twice" (.open "rep2" group
    (.records #[encode a2, encode a1, encode c1, encode b1, encode a1])) .ok,
  ask "ENCODE rep2: a1 counts once" (.encode "rep2") .ok (some (.blob (s3 all4.encode))),
  ask "OPEN a doctored blob (b1 cut out): unverifiable a2, missing b1"
    (.open "bad" group (.blob (s3 (encodeBlob group #[a1, c1, a2])))) .unverifiable
    (some (.opened (.error (.unverifiable #[hashRecord a2] #[hashRecord b1])))),
  ask "HEADS bad: nothing was loaded" (.heads "bad") .noChat,
  ask "OPEN bytes that are not a blob" (.open "bad" group (.blob "junk".toUTF8)) .malformed,
  ask "OPEN a zrdtS2 blob: only zrdtS3 is read" (.open "bad" group (.blob all4.encode)) .malformed,
  ask "OPEN a blob of another group" (.open "bad" group (.blob (s3 (encodeBlob otherGroup #[]))))
    .wrongChat,
  ask "OPEN a list with a record of another group" (.open "bad" group
    (.records #[encode a1, encode foreign])) .wrongChat,
  ask "OPEN a list with a record that does not decode" (.open "bad" group badList) .malformed,
  ask "SALVAGE the doctored blob: dropped a2, missing b1" (.salvage "kept" group
    (.blob (s3 (encodeBlob group #[a1, c1, a2])))) .ok
    (some (.salvaged (.ok (#[hashRecord a2], #[hashRecord b1])))),
  ask "HEADS kept: c1" (.heads "kept") .ok (some (.digests #[hashRecord c1])),
  ask "SALVAGE kept again: already open" (.salvage "kept" group (.blob (s3 all4.encode)))
    .chatOpen,
  ask "SALVAGE the doctored blob with a2 twice: a2 dropped once" (.salvage "kept3" group
    (.blob (s3 (encodeBlob group #[a2, a1, c1, a2])))) .ok
    (some (.salvaged (.ok (#[hashRecord a2], #[hashRecord b1])))),
  ask "SALVAGE a list: nothing to drop" (.salvage "kept2" group
    (.records #[encode c1, encode a1])) .ok (some (.salvaged (.ok (#[], #[])))),
  ask "SALVAGE bytes that are not a blob" (.salvage "bad" group (.blob "junk".toUTF8)) .malformed,
  ask "SALVAGE a blob of another group"
    (.salvage "bad" group (.blob (s3 (encodeBlob otherGroup #[]))))
    .wrongChat,
  ask "SALVAGE a list with a record that does not decode" (.salvage "bad" group badList)
    .malformed,
  ask "MERGE the doctored blob into kept: unverifiable, kept unchanged"
    (.merge "kept" (s3 (encodeBlob group #[a1, c1, a2]))) .unverifiable,
  ask "MERGE a blob of another group: wrong chat" (.merge "kept" (s3 (encodeBlob otherGroup #[])))
    .wrongChat,
  ask "MERGE bytes that are not a blob" (.merge "kept" "junk".toUTF8) .malformed,
  ask "HEADS kept: still c1" (.heads "kept") .ok (some (.digests #[hashRecord c1])),
  ask "MERGE a1 b1 into kept" (.merge "kept" (s3 storeAB.encode)) .ok,
  ask "HEADS kept: b1 and c1" (.heads "kept") .ok
    (some (.digests (sorted #[hashRecord b1, hashRecord c1]))),
  ask "MERGE into a chat that is not open" (.merge "nochat" (s3 storeAB.encode)) .noChat,
  ask "ACCEPT into a chat that is not open" (.accept "nochat" (.ofRec m1) m1Opened.2) .noChat,
  ask "HAS in a chat that is not open" (.has "nochat" (dig 1)) .noChat,
  ask "GET in a chat that is not open" (.get "nochat" (dig 1)) .noChat,
  ask "REACH_SET in a chat that is not open" (.reachSet "nochat" #[]) .noChat,
  ask "CLASSIFY in a chat that is not open" (.classify "nochat" #[]) .noChat,
  ask "ENCODE in a chat that is not open" (.encode "nochat") .noChat,
  ask "CLOSE kept" (.close "kept") .ok,
  ask "CLOSE kept again: still OK" (.close "kept") .ok,
  ask "HEADS kept after CLOSE" (.heads "kept") .noChat,
  ask "NEW kept: the key is free again" (.new "kept" group) .ok,
  ask "HEADS kept: empty" (.heads "kept") .ok (some (.digests #[]))]

/-- A record with 4097 links, one more than allowed (`Zrdt.Examples.tooManyLinks`). -/
def tooLargeSteps : Array Step := #[
  ask "NEW big" (.new "big" group) .ok,
  ask "ACCEPT a record with 4097 links, with its opening" (.accept "big" (.ofRec m1TooLarge)
    m1Opened.2) .tooLarge,
  ask "HEADS big: still empty" (.heads "big") .ok (some (.digests #[])),
  ask "OPEN a list holding a record with 4097 links" (.open "big2" group
    (.records #[encode tooManyLinks])) .tooLarge]

/-- `ACCEPT_RECORD`: records that come as bytes (relayed, imported), with or without an
opening. -/
def acceptRecordSteps : Array Step := #[
  ask "ACCEPT_RECORD before NEW: no chat" (.acceptRecord "r" (encode a1) none) .noChat,
  ask "NEW r" (.new "r" group) .ok,
  ask "ACCEPT_RECORD m1 with its opening, before a1: missing a1"
    (.acceptRecord "r" (encode m1) (some m1Opened.2)) .missing
    (some (.accept m1 (.missing #[hashRecord a1]))),
  ask "ACCEPT_RECORD a1 without an opening (structure only)" (.acceptRecord "r" (encode a1) none)
    .ok (some (.accept a1 (.accepted (hashRecord a1)))),
  ask "ACCEPT_RECORD m1 with an opening that still holds field 15: bad opening"
    (.acceptRecord "r" (encode m1) (some (nonce.bytes ++ dataMessage))) .badOpening,
  ask "ACCEPT_RECORD m1 with an opening cut inside the nonce: bad opening"
    (.acceptRecord "r" (encode m1) (some (m1Opened.2.extract 0 31))) .badOpening,
  ask "ACCEPT_RECORD m1 with the opening of another message: bad opening"
    (.acceptRecord "r" (encode m1) (some (nonce.bytes ++ bodyField))) .badOpening,
  ask "ACCEPT_RECORD m1 in Bob's name with Alice's opening: bad opening"
    (.acceptRecord "r" (encode m1AsBob) (some m1Opened.2)) .badOpening,
  ask "ACCEPT_RECORD m0 with its opening, which has no audience (field 201): no audience"
    (.acceptRecord "r" (encode m0) (some m0Opened.2)) .noAudience,
  ask "ACCEPT m0 with its opening: no audience" (.accept "r" (.ofRec m0) m0Opened.2)
    .noAudience,
  ask "ACCEPT m1 with the opening of m0: bad opening" (.accept "r" (.ofRec m1) m0Opened.2)
    .badOpening,
  ask "HEADS r: still a1" (.heads "r") .ok (some (.digests #[hashRecord a1])),
  ask "ACCEPT_RECORD m1 with its opening" (.acceptRecord "r" (encode m1) (some m1Opened.2)) .ok
    (some (.accept m1 (.accepted (hashRecord m1)))),
  ask "ACCEPT_RECORD m1 again, without the opening: accepted, nothing changes"
    (.acceptRecord "r" (encode m1) none) .ok (some (.accept m1 (.accepted (hashRecord m1)))),
  ask "HEADS r: m1" (.heads "r") .ok (some (.digests #[hashRecord m1])),
  ask "ACCEPT_RECORD bytes that are not a record" (.acceptRecord "r" ((encode a1).push 0) none)
    .malformed,
  ask "ACCEPT_RECORD a record whose links are out of order" (.acceptRecord "r"
    ((bytesOfHex? (twoLinksHex "02" "01")).getD .empty) none) .malformed,
  ask "ACCEPT_RECORD a record of another group" (.acceptRecord "r" (encode foreign) none)
    .wrongChat,
  ask "ACCEPT_RECORD a record with 4097 links" (.acceptRecord "r" (encode tooManyLinks) none)
    .tooLarge,
  ask "ACCEPT_RECORD m1 into a chat that is not open" (.acceptRecord "nochat" (encode m1)
    (some m1Opened.2)) .noChat,
  ask "HEADS r: still m1" (.heads "r") .ok (some (.digests #[hashRecord m1])),
  ask "NEW live (ACCEPT: a live record, always with its opening)" (.new "live" group) .ok,
  ask "ACCEPT m1 with its opening, before a1: missing a1" (.accept "live" (.ofRec m1) m1Opened.2)
    .missing (some (.accept m1 (.missing #[hashRecord a1]))),
  ask "ACCEPT with an empty opening: bad opening" (.accept "live" (.ofRec m1) .empty) .badOpening,
  ask "ACCEPT_RECORD a1 (structure only)" (.acceptRecord "live" (encode a1) none) .ok,
  ask "ACCEPT m1 with its opening, its link given twice: the canonical encoding comes back"
    (.accept "live" ⟨group, m1.commit, #[hashRecord a1, hashRecord a1], alice⟩ m1Opened.2) .ok
    (some (.accept m1 (.accepted (hashRecord m1)))),
  ask "ADDRESSED bob in live: m1, its audience recorded" (.addressed "live" bob keyBob) .ok
    (some (.digests #[hashRecord m1])),
  ask "ACCEPT a record of another group, with its opening: wrong chat"
    (.accept "live" (.ofRec m1Foreign) m1ForeignOpened.2) .wrongChat,
  ask "HEADS live: m1" (.heads "live") .ok (some (.digests #[hashRecord m1]))]


/-! ### `AUDIENCE`, `SERVE`, `ADDRESSED` (docs/JOIN_PLAN.md §3–§5)

Chat `g` holds the four records of `Serve.Examples`: Carol's `pre` (before Bob joined; audience
Alice and Carol), Alice's `welcome` (Bob seated), Carol's `stale` (her view lagged the add: Bob
not seated) and Alice's `later` (Bob seated). Alice answers. In each `SERVE` below, the host also
passes `pre`'s opening: the leak attempt. The reply must carry `pre` as a digest only. -/

/-- The request id of the `SERVE` steps. -/
def rid : ByteArray := ⟨Array.replicate 16 0x1d⟩

/-- The records of chat `g`, with their openings. -/
def joinRecords : Array (Rec × ByteArray) := #[pre, welcome, stale, later]

/-- A `SERVE` request from Alice's device to `to` under `key`; she holds every opening, and her
own records `live`. -/
def serveFrom (to : Aci) (key : ByteArray) (wanted : Option (Array Digest) := none)
    (since : Array Digest := #[]) (forExport := false) (strict := false)
    (records : Array (Rec × ByteArray) := joinRecords) : ServeRequest :=
  { own := alice, requester := to, key, rid, since, ownSince := #[], wanted, forExport, strict,
    live := #[hashRecord welcome.1, hashRecord later.1, hashRecord timed.1], disown := #[],
    held := records.map fun (r, o) => (hashRecord r, o) }

/-- The entries of a `SERVE` reply computed from `Serve.serve` directly, for a closed store
holding `records` with the audiences of their openings recorded. -/
def serveEntries (sr : ServeRequest) (records : Array (Rec × ByteArray) := joinRecords) :
    List Serve.Entry :=
  let c := ((CheckedStore.empty group).acceptAll (records.map (·.1))).1
  let auds : Std.ExtTreeMap Digest (Array Serve.Seat) compare :=
    records.foldl (init := ∅) fun m (r, o) =>
      match Serve.audienceOf o with
      | some a => m.insert (hashRecord r) a
      | none => m
  Serve.serve c.raw sr.me (sr.heldMap auds) sr.query

/-- The `SERVE` reply computed from `Serve.serve` directly (`serveEntries`). -/
def expectServe (sr : ServeRequest) (records : Array (Rec × ByteArray) := joinRecords) : Reply :=
  .served ⟨sr.requester, Serve.keyTag sr.key, sr.rid⟩ (serveEntries sr records)

/-- Whether `needle` occurs in `hay`. -/
def containsBytes (hay needle : ByteArray) : Bool :=
  (List.range (hay.size + 1 - needle.size)).any fun i =>
    hay[i]? == needle[0]? && hay.extract i (i + needle.size) == needle

#guard containsBytes ⟨#[1, 2, 3]⟩ ⟨#[2, 3]⟩ && !containsBytes ⟨#[1, 2, 3]⟩ ⟨#[3, 2]⟩

/-- The digests of some records, sorted. -/
def digestsOf (rs : List (Rec × ByteArray)) : Array Digest := sorted (rs.map (hashRecord ·.1)).toArray

/-- 257 members, each with no key. -/
def tooManyMembers : Array (Aci × Option ByteArray) :=
  (List.range 257).toArray.map fun i =>
    (⟨⟨Array.replicate 14 0 ++ #[(i / 256).toUInt8, (i % 256).toUInt8]⟩, rfl⟩, none)

/-- Chat `g` of the session below at its `ENCODE`: the four records and the disappearing message,
with their audiences. -/
def gBlob : ByteArray :=
  let rs := joinRecords.push timed
  let c := ((CheckedStore.empty group).acceptAll (rs.map (·.1))).1
  let auds : AudTable := rs.foldl (init := ∅) fun m (r, o) =>
    match Serve.audienceOf o with
    | some a => m.insert (hashRecord r) a
    | none => m
  encodeChat (.closed c) auds

/-- The session. -/
def joinSteps : Array Step := #[
  ask "NEW g" (.new "g" group) .ok,
  ask "AUDIENCE carol and alice, given out of order: sorted, each with its key tag"
    (.audience #[(carol, some keyCarol), (alice, some keyAlice)]) .ok
    (some (.audience (Serve.writeAudience (audienceOfKeys AC)))),
  ask "AUDIENCE alice, bob, carol, and mallory with no key (blocked): the zero tag for mallory"
    (.audience #[(mallory, none), (bob, some keyBob), (alice, some keyAlice),
      (carol, some keyCarol)]) .ok
    (some (.audience (Serve.writeAudience (audienceOfKeys
      [(alice, some keyAlice), (bob, some keyBob), (carol, some keyCarol), (mallory, none)])))),
  ask "AUDIENCE with no members: malformed" (.audience #[]) .malformed,
  ask "AUDIENCE with alice twice: malformed"
    (.audience #[(alice, some keyAlice), (alice, none)]) .malformed,
  ask "AUDIENCE with 257 members: too large" (.audience tooManyMembers) .tooLarge,
  ask "COMMIT Carol's pre-join message (its field 201 is the first AUDIENCE reply)"
    (.commit group carol (Serve.Examples.nonceOf 1) (Serve.Examples.message "pre-join secret" AC))
    .ok (some (.committed pre.1.commit pre.2)),
  ask "ACCEPT pre with its opening: its audience is recorded" (.accept "g" (.ofRec pre.1)
    pre.2) .ok (some (.accept pre.1 (.accepted (hashRecord pre.1)))),
  ask "ACCEPT welcome with its opening" (.accept "g" (.ofRec welcome.1) welcome.2) .ok,
  ask "ACCEPT stale with its opening" (.accept "g" (.ofRec stale.1) stale.2) .ok,
  ask "ACCEPT_RECORD later with its opening" (.acceptRecord "g" (encode later.1) (some later.2))
    .ok,
  ask "ACCEPT later with the opening of welcome: bad opening" (.accept "g" (.ofRec later.1)
    welcome.2) .badOpening,
  ask "ACCEPT_RECORD of a message without field 201, with its opening: no audience"
    (.acceptRecord "g" (encode noAudience.1) (some noAudience.2)) .noAudience,
  ask "ADDRESSED bob under his key: welcome and later" (.addressed "g" bob keyBob) .ok
    (some (.digests (digestsOf [welcome, later]))),
  ask "ADDRESSED bob under a swapped key: nothing" (.addressed "g" bob keyBob') .ok
    (some (.digests #[])),
  ask "ADDRESSED carol: all four" (.addressed "g" carol keyCarol) .ok
    (some (.digests (digestsOf [pre, welcome, stale, later]))),
  ask "SERVE catch-up to bob, the host passing pre's opening too: welcome and later with content, stale as structure, pre as a digest"
    (.serve "g" (serveFrom bob keyBob)) .ok (some (expectServe (serveFrom bob keyBob))),
  ask "SERVE per-digest to bob, asking for pre: pre as a digest only"
    (.serve "g" (serveFrom bob keyBob (wanted := some #[hashRecord pre.1]))) .ok
    (some (expectServe (serveFrom bob keyBob (wanted := some #[hashRecord pre.1])))),
  ask "SERVE catch-up to bob with since = later: no content of pre, nothing about pre"
    (.serve "g" (serveFrom bob keyBob (since := #[hashRecord later.1]))) .ok,
  ask "SERVE to bob under a swapped key: no content at all"
    (.serve "g" (serveFrom bob keyBob')) .ok
    (some (expectServe (serveFrom bob keyBob'))),
  ask "SERVE to carol: content of all four"
    (.serve "g" (serveFrom carol keyCarol)) .ok
    (some (expectServe (serveFrom carol keyCarol))),
  ask "SERVE to carol in strict mode: content only for Alice's own (welcome, later)"
    (.serve "g" (serveFrom carol keyCarol (strict := true))) .ok
    (some (expectServe (serveFrom carol keyCarol (strict := true)))),
  ask "ACCEPT a disappearing message to alice, bob and carol, with its opening"
    (.accept "g" (.ofRec timed.1) timed.2) .ok,
  ask "SERVE an export for bob, built on Alice's device (requester bob, export flag): the disappearing message goes without content"
    (.serve "g" (serveFrom bob keyBob (forExport := true) (records := joinRecords.push timed))) .ok
    (some (expectServe (serveFrom bob keyBob (forExport := true) (records := joinRecords.push timed))
      (joinRecords.push timed))),
  ask "SERVE a relay to bob: the disappearing message goes with content"
    (.serve "g" (serveFrom bob keyBob (records := joinRecords.push timed))) .ok
    (some (expectServe (serveFrom bob keyBob (records := joinRecords.push timed))
      (joinRecords.push timed))),
  ask "SERVE in a chat that is not open" (.serve "nochat" (serveFrom bob keyBob)) .noChat,
  ask "ADDRESSED in a chat that is not open" (.addressed "nochat" bob keyBob) .noChat,
  ask "OPEN g2 from g's records: no audiences recorded yet"
    (.open "g2" group (.records (joinRecords.map (encode ·.1)))) .ok,
  ask "ADDRESSED bob in g2: nothing" (.addressed "g2" bob keyBob) .ok (some (.digests #[])),
  ask "ACCEPT_RECORD welcome again in g2, with its opening: accepted, its audience recorded"
    (.acceptRecord "g2" (encode welcome.1) (some welcome.2)) .ok
    (some (.accept welcome.1 (.accepted (hashRecord welcome.1)))),
  ask "ADDRESSED bob in g2: welcome" (.addressed "g2" bob keyBob) .ok
    (some (.digests #[hashRecord welcome.1])),
  ask "ENCODE g: the blob carries the audiences" (.encode "g") .ok (some (.blob gBlob)),
  ask "OPEN g3 from g's blob" (.open "g3" group (.blob gBlob)) .ok,
  ask "ADDRESSED bob in g3: the audiences came back with the blob" (.addressed "g3" bob keyBob) .ok
    (some (.digests (digestsOf [welcome, later, timed]))),
  ask "MERGE g's blob into g2: the blob's audiences are recorded where none is"
    (.merge "g2" gBlob) .ok,
  ask "ADDRESSED bob in g2: the merged audiences too (later, and the new disappearing message)"
    (.addressed "g2" bob keyBob) .ok (some (.digests (digestsOf [welcome, later, timed]))),
  ask "ENCODE g2: the same blob as g's" (.encode "g2") .ok (some (.blob gBlob)),
  ask "CLOSE g" (.close "g") .ok,
  ask "NEW g again: no audiences" (.new "g" group) .ok,
  ask "ADDRESSED carol in the new g: nothing" (.addressed "g" carol keyCarol) .ok
    (some (.digests #[]))]

/-- The checks on the `join` session's replies, given the steps and their replies (run once). -/
def joinChecks (out : List (Step × ByteArray)) : Bool :=
  let reply (name : String) : ByteArray := (out.find? (·.1.name == name)).elim .empty (·.2)
  -- The leak attempt: no `SERVE` reply to Bob carries `pre`'s opening, though the host passed it.
  (out.all fun (st, r) => st.request[0]? != some 0x12 || !containsBytes r pre.2 ||
    reply "SERVE to carol: content of all four" == r) &&
  containsBytes (reply ("SERVE catch-up to bob, the host passing pre's opening too: welcome " ++
    "and later with content, stale as structure, pre as a digest")) welcome.2 &&
  !containsBytes (reply "SERVE to bob under a swapped key: no content at all") welcome.2 &&
  containsBytes (reply "SERVE to carol: content of all four") pre.2 &&
  !containsBytes (reply "SERVE to carol in strict mode: content only for Alice's own (welcome, later)")
    pre.2 &&
  containsBytes (reply "SERVE to carol in strict mode: content only for Alice's own (welcome, later)")
    welcome.2 &&
  !containsBytes (reply ("SERVE an export for bob, built on Alice's device (requester bob, " ++
    "export flag): the disappearing message goes without content")) timed.2 &&
  containsBytes (reply "SERVE a relay to bob: the disappearing message goes with content") timed.2 &&
  -- The reply header: bob's ACI, the tag of his key, the request id; then pre as a digest only.
  reply "SERVE per-digest to bob, asking for pre: pre as a digest only" ==
    ⟨#[0]⟩ ++ bob.bytes ++ ⟨Serve.keyTag keyBob⟩ ++ rid ++ u32be 1 ++ ⟨#[2]⟩ ++
      (hashRecord pre.1).bytes

#guard joinChecks (joinSteps.toList.zip (session (joinSteps.map (·.request)).toList))

/-! ### Relative stores: `NEW_RELATIVE`, `ACCEPT_VIEW`, `LINKABLE` (docs/JOIN_PLAN.md §4.4, §6)

Bob joined chat `g` after `pre`. Alice's catch-up reply to him (the first `SERVE` of the `join`
session) carries `welcome` and `later` with content, `stale` as structure, and `pre` as a digest.
Bob's device opens a relative store and passes the reply's entries to `ACCEPT_VIEW`, byte for
byte. Then Bob, a former newcomer, answers Carol: his reply carries his own boundary digest, and a
second-generation newcomer that accepts it has the same heads as everyone. -/

/-- Alice's chat `g`: the four records. -/
def storeG : CheckedStore := ((CheckedStore.empty group).acceptAll (joinRecords.map (·.1))).1

/-- The audiences of `g`'s records. -/
def audsG : AudTable := joinRecords.foldl (init := ∅) fun m (r, o) =>
  match Serve.audienceOf o with
  | some a => m.insert (hashRecord r) a
  | none => m

/-- Alice's catch-up reply to Bob: its entries. -/
def aliceToBob : List Serve.Entry :=
  let sr := serveFrom bob keyBob
  Serve.serve storeG.raw sr.me (sr.heldMap audsG) sr.query

/-- A `SERVE` entry as `ACCEPT_VIEW` reads it. -/
def toView : Serve.Entry → ViewEntry
  | .addressed r o ac => .addressed (encode r) ac o
  | .after r => .after (encode r)
  | .boundary d => .boundary d

-- The host passes the bytes after the `SERVE` header to `ACCEPT_VIEW` unchanged: the layouts are
-- the same.
#guard Write.viewEntries (aliceToBob.map toView).toArray == Write.entries aliceToBob

/-- What `ACCEPT_VIEW` replies when it takes every entry. -/
def allTaken (es : List Serve.Entry) : Reply :=
  .viewed (es.map fun
    | .addressed r _ _ | .after r => .record (.accepted (hashRecord r))
    | .boundary d => .known d).toArray

/-- Bob's chat after the catch-up. -/
def bobChat : Chat :=
  (acceptView { store := .relative (.empty group) } alice false false
    (aliceToBob.map toView).toArray).2

/-- Bob's blob. -/
def bobBlob : ByteArray := encodeChat bobChat.store bobChat.audiences

/-- Bob's reply to Carol's catch-up: he holds the openings he was sent. -/
def bobServe : ServeRequest :=
  { own := bob, requester := carol, key := keyCarol, rid, since := #[], ownSince := #[],
    wanted := none, forExport := false, strict := false, live := #[], disown := #[],
    held := #[(hashRecord welcome.1, welcome.2), (hashRecord later.1, later.2)] }

/-- Bob's reply to Carol: its entries. -/
def bobToCarol : List Serve.Entry :=
  Serve.serve bobChat.store.raw (bobServe.me bobChat.store.boundaryDigests)
    (bobServe.heldMap bobChat.audiences) bobServe.query

-- Bob's reply: `welcome` and `later` with content, `stale` as structure, `pre` as his own boundary
-- digest (the round-1 fix for second-generation newcomers).
#guard Serve.Examples.contentOf bobToCarol == [welcome.1, later.1] ||
  Serve.Examples.contentOf bobToCarol == [later.1, welcome.1]
#guard Serve.Examples.afterOf bobToCarol == [stale.1]
#guard Serve.Examples.boundaryOf bobToCarol == [hashRecord pre.1]

/-- The export Alice's device builds for Bob's account (JOIN_PLAN §4.5): `SERVE` with Bob as the
requester, under the key Alice holds for him, with the export flag. Only what Bob is seated in
comes with content; `pre` comes as a digest, the disappearing message without content. -/
def aliceExportForBob : List Serve.Entry :=
  serveEntries (serveFrom bob keyBob (forExport := true) (records := joinRecords.push timed))
    (joinRecords.push timed)

#guard Serve.Examples.contentOf aliceExportForBob == [welcome.1, later.1] ||
  Serve.Examples.contentOf aliceExportForBob == [later.1, welcome.1]
#guard Serve.Examples.boundaryOf aliceExportForBob == [hashRecord pre.1]
#guard !containsBytes (Write.entries aliceExportForBob) pre.2 &&
  !containsBytes (Write.entries aliceExportForBob) timed.2

/-- `CLASSIFY` of Bob's relative store with no facts: every record unconfirmed. -/
def bobStatuses : Array (Digest × Status) :=
  (digestsOf [welcome, stale, later]).map fun d => (d, .unconfirmed)

/-- The session. -/
def viewSteps : Array Step := #[
  ask "NEW_RELATIVE bob" (.newRelative "bob" group) .ok,
  ask "NEW_RELATIVE bob again: already open" (.newRelative "bob" group) .chatOpen,
  ask "HEADS of an empty relative store" (.heads "bob") .ok (some (.digests #[])),
  { name := "ACCEPT_VIEW bob, vouched by alice, catch-up mode: the entries of Alice's SERVE reply, byte for byte, no pending"
    request := Write.u8 0x14 ++ Write.str "bob" ++ alice.bytes ++ Write.u8 0 ++ Write.u8 0 ++
      Write.entries aliceToBob ++ u32be 0
    expect := .ok, reply? := some (allTaken aliceToBob).write },
  ask "HEADS bob: Alice's heads (later)" (.heads "bob") .ok
    (some (.digests storeG.headsArray)),
  ask "HAS bob pre: a boundary digest, not a record" (.has "bob" (hashRecord pre.1)) .ok
    (some (.has false)),
  ask "GET bob pre: not found" (.get "bob" (hashRecord pre.1)) .notFound,
  ask "REACH_SET bob from later: the three records" (.reachSet "bob" #[hashRecord later.1]) .ok
    (some (.digests (digestsOf [welcome, stale, later]))),
  ask "ADDRESSED bob under his key: the two records sent to him" (.addressed "bob" bob keyBob) .ok
    (some (.digests (digestsOf [welcome, later]))),
  ask "LINKABLE bob with nothing live: no link" (.linkable "bob" #[]) .ok (some (.digests #[])),
  ask "LINKABLE bob with later live (Alice's author copy): later"
    (.linkable "bob" #[hashRecord welcome.1, hashRecord later.1]) .ok
    (some (.digests #[hashRecord later.1])),
  ask "CLASSIFY bob with no facts" (.classify "bob" #[]) .ok (some (.classified bobStatuses)),
  ask "ENCODE bob: a relative zrdtS3 blob" (.encode "bob") .ok (some (.blob bobBlob)),
  ask "OPEN bob2 from Bob's blob" (.open "bob2" group (.blob bobBlob)) .ok,
  ask "HEADS bob2: the same heads" (.heads "bob2") .ok (some (.digests storeG.headsArray)),
  ask "ENCODE bob2: the same blob" (.encode "bob2") .ok (some (.blob bobBlob)),
  ask "ADDRESSED bob in bob2: the audiences came back" (.addressed "bob2" bob keyBob) .ok
    (some (.digests (digestsOf [welcome, later]))),
  ask "SALVAGE bob3 from Bob's blob: nothing dropped" (.salvage "bob3" group (.blob bobBlob)) .ok
    (some (.salvaged (.ok (#[], #[])))),
  ask "SERVE from Bob's relative store to Carol: his boundary digest goes too"
    (.serve "bob" bobServe) .ok
    (some (.served ⟨carol, Serve.keyTag keyCarol, rid⟩ bobToCarol)),
  ask "NEW_RELATIVE carol2 (a second-generation newcomer)" (.newRelative "carol2" group) .ok,
  ask "ACCEPT_VIEW carol2 vouched by bob" (.acceptView "carol2" bob false false
    (bobToCarol.map toView).toArray #[]) .ok (some (allTaken bobToCarol)),
  ask "HEADS carol2: the same heads again" (.heads "carol2") .ok
    (some (.digests storeG.headsArray)),
  ask "NEW closed" (.new "closed" group) .ok,
  ask "ACCEPT_VIEW into a closed store: pre ignored, so nothing resolves"
    (.acceptView "closed" alice false false (aliceToBob.map toView).toArray #[]) .ok,
  ask "HEADS closed: still empty" (.heads "closed") .ok (some (.digests #[])),
  ask "MERGE Bob's relative blob into the closed store: unverifiable, pre missing"
    (.merge "closed" bobBlob) .unverifiable
    (some (.opened (.error (.unverifiable (digestsOf [welcome, stale, later])
      #[hashRecord pre.1])))),
  ask "ACCEPT_VIEW pre's record into the closed store, then Alice's view: all taken"
    (.acceptView "closed" alice false false
      (#[.after (encode pre.1)] ++ (aliceToBob.map toView).toArray) #[]) .ok,
  ask "LINKABLE of a closed store: its heads" (.linkable "closed" #[]) .ok
    (some (.digests storeG.headsArray)),
  ask "ACCEPT_VIEW bob, per-digest from carol: pre's record arrives (promotion)"
    (.acceptView "bob" carol false true #[.after (encode pre.1)] #[]) .ok (some (.viewed #[.record (.accepted (hashRecord pre.1))])),
  ask "HAS bob pre: now a record" (.has "bob" (hashRecord pre.1)) .ok (some (.has true)),
  ask "HEADS bob: unchanged" (.heads "bob") .ok (some (.digests storeG.headsArray)),
  ask "ACCEPT_VIEW bob: later with welcome's opening" (.acceptView "bob" alice false false
    #[.addressed (encode later.1) true (some welcome.2)] #[]) .ok
    (some (.viewed #[.code .badOpening])),
  ask "ACCEPT_VIEW bob: bytes that are not a record" (.acceptView "bob" alice false false
    #[.after ((encode later.1).push 0)] #[]) .ok (some (.viewed #[.code .malformed])),
  ask "ACCEPT_VIEW bob: an opening without field 201" (.acceptView "bob" alice false false
    #[.addressed (encode noAudience.1) false (some noAudience.2)] #[]) .ok
    (some (.viewed #[.code .noAudience])),
  ask "ACCEPT_VIEW bob, an import: a disappearing message is refused" (.acceptView "bob" alice
    true false #[.addressed (encode timed.1) false (some timed.2)] #[]) .ok
    (some (.viewed #[.code .ephemeral])),
  ask "ACCEPT_VIEW bob, a relay: the disappearing message is taken" (.acceptView "bob" alice
    false false #[.addressed (encode timed.1) false (some timed.2)] #[]) .ok
    (some (.viewed #[.record (.accepted (hashRecord timed.1))])),
  ask "ACCEPT_VIEW bob: a record of another chat, and one whose link is unknown"
    (.acceptView "bob" alice false false #[.after (encode foreign), .after (encode b1)] #[]) .ok
    (some (.viewed #[.record .wrongChat, .record (.missing #[hashRecord a1])])),
  ask "ACCEPT_VIEW in a chat that is not open" (.acceptView "nochat" alice false false #[] #[])
    .noChat,
  ask "LINKABLE in a chat that is not open" (.linkable "nochat" #[]) .noChat,
  ask "MERGE a closed store's blob into bob" (.merge "bob" (s3 storeAB.encode)) .ok,
  ask "HAS bob b1" (.has "bob" (hashRecord b1)) .ok (some (.has true)),
  ask "NEW_RELATIVE bobx: Bob's device imports the export Alice built for his account"
    (.newRelative "bobx" group) .ok,
  ask "ACCEPT_VIEW bobx, an import (catch-up mode, vouched by alice): all taken"
    (.acceptView "bobx" alice true false (aliceExportForBob.map toView).toArray #[]) .ok
    (some (allTaken aliceExportForBob)),
  ask "ADDRESSED bob in bobx: welcome and later; the disappearing message came without content"
    (.addressed "bobx" bob keyBob) .ok (some (.digests (digestsOf [welcome, later]))),
  ask "HAS bobx pre: a boundary digest only" (.has "bobx" (hashRecord pre.1)) .ok
    (some (.has false))]

/-- The checks on the `view` session's replies. -/
def viewChecks (out : List (Step × ByteArray)) : Bool :=
  let reply (name : String) : ByteArray := (out.find? (·.1.name == name)).elim .empty (·.2)
  -- A closed store ignores the boundary entry, and the records that need it are missing.
  reply "ACCEPT_VIEW into a closed store: pre ignored, so nothing resolves" ==
    (Reply.viewed (aliceToBob.map fun
      | .boundary d => .code (if d == hashRecord pre.1 then .ignored else .ok)
      | .addressed r _ _ | .after r =>
        .record (.missing #[(r.links[0]?).getD Digest.zero])).toArray).write &&
  reply "ACCEPT_VIEW pre's record into the closed store, then Alice's view: all taken" ==
    (Reply.viewed (#[.record (.accepted (hashRecord pre.1))] ++ (aliceToBob.map fun
      | .boundary d => ViewResult.known d
      | .addressed r _ _ | .after r => .record (.accepted (hashRecord r))).toArray)).write

#guard viewChecks (viewSteps.toList.zip (session (viewSteps.map (·.request)).toList))

/-! ### Boundary admission: a per-digest reply adds no stray head (docs/JOIN_PLAN.md §4.4)

Chat `s` at Alice: Carol's `older` and `newer` (before Bob joined: audience Alice and Carol), then
Alice's `hi` (Bob seated), which links `newer`. Bob catches up from Alice: `hi` with content,
`newer` as a boundary digest; his heads are Alice's (`hi`). Then Bob asks Alice by name for
`older`, as beat 6 of the smoke does: the reply carries `older` as a digest only, and no record of
Bob's links it. Taken in per-digest mode it is dropped (`IGNORED`) and his heads stay Alice's.
Taken as protocol 3 took it (every boundary entry, here catch-up mode on a copy of his store),
`older` becomes a head that no record will ever link: the stray head of the round-2 review. Then
Carol's late message `lateC`, written from an old view, links `older`: Bob's `ACCEPT` of it is
`MISSING older`; he asks Alice for `older` again and passes `lateC` as pending with her reply: both
are taken, and his heads are Alice's again. -/

/-- Carol, long before Bob joined. -/
def older : Rec × ByteArray := Serve.Examples.mk carol 40 "older pre-join" AC #[]
/-- Carol, before Bob joined. -/
def newer : Rec × ByteArray := Serve.Examples.mk carol 41 "newer pre-join" AC #[hashRecord older.1]
/-- Alice, after the add: Bob seated. -/
def hi : Rec × ByteArray := Serve.Examples.mk alice 42 "hi bob" ABC #[hashRecord newer.1]
/-- Carol after the add, from an old view: Bob seated, but it links `older`. -/
def lateC : Rec × ByteArray :=
  Serve.Examples.mk carol 43 "late, from an old view" ABC #[hashRecord older.1]

/-- Chat `s` at Alice before `lateC`. -/
def strayRecords : Array (Rec × ByteArray) := #[older, newer, hi]

/-- Alice's catch-up reply to Bob. -/
def strayCatchUp : List Serve.Entry :=
  serveEntries (serveFrom bob keyBob (records := strayRecords)) strayRecords

/-- Alice's per-digest reply to Bob, who asks for `older`: the digest only. -/
def strayOlder : List Serve.Entry :=
  serveEntries (serveFrom bob keyBob (wanted := some #[hashRecord older.1]) (records := strayRecords))
    strayRecords

#guard Write.entries strayOlder == Write.entries [.boundary (hashRecord older.1)]
#guard Serve.Examples.boundaryOf strayCatchUp == [hashRecord newer.1] &&
  Serve.Examples.contentOf strayCatchUp == [hi.1]

/-- A record of another chat that links digest `77…`. -/
def foreignLinking : Rec := Rec.make otherGroup (dig 0xd2) #[dig 0x77] alice

/-- A record that links digests `78…` and `79…`. -/
def twoUnknown : Rec := Rec.make group (dig 0xd3) #[dig 0x78, dig 0x79] alice

/-- The session. -/
def boundarySteps : Array Step := #[
  ask "NEW s (Alice's store)" (.new "s" group) .ok,
  ask "ACCEPT older" (.accept "s" (.ofRec older.1) older.2) .ok,
  ask "ACCEPT newer" (.accept "s" (.ofRec newer.1) newer.2) .ok,
  ask "ACCEPT hi" (.accept "s" (.ofRec hi.1) hi.2) .ok,
  ask "HEADS s: hi" (.heads "s") .ok (some (.digests #[hashRecord hi.1])),
  ask "SERVE catch-up to bob: hi with content, newer as a digest"
    (.serve "s" (serveFrom bob keyBob (records := strayRecords))) .ok
    (some (expectServe (serveFrom bob keyBob (records := strayRecords)) strayRecords)),
  ask "SERVE per-digest to bob, asking for older: older as a digest only"
    (.serve "s" (serveFrom bob keyBob (wanted := some #[hashRecord older.1])
      (records := strayRecords))) .ok
    (some (.served ⟨bob, Serve.keyTag keyBob, rid⟩ strayOlder)),
  ask "NEW_RELATIVE b (Bob)" (.newRelative "b" group) .ok,
  ask "ACCEPT_VIEW b, catch-up mode: all taken"
    (.acceptView "b" alice false false (strayCatchUp.map toView).toArray #[]) .ok
    (some (allTaken strayCatchUp)),
  ask "HEADS b: Alice's (hi)" (.heads "b") .ok (some (.digests #[hashRecord hi.1])),
  ask "NEW_RELATIVE b3 (a copy of Bob's store, for the rule of protocol 3)"
    (.newRelative "b3" group) .ok,
  ask "ACCEPT_VIEW b3, catch-up mode" (.acceptView "b3" alice false false
    (strayCatchUp.map toView).toArray #[]) .ok (some (allTaken strayCatchUp)),
  ask "ACCEPT_VIEW b, per-digest mode, the reply for older: no record links it, so it is ignored"
    (.acceptView "b" alice false true (strayOlder.map toView).toArray #[]) .ok
    (some (.viewed #[.code .ignored])),
  ask "HEADS b: still Alice's (hi)" (.heads "b") .ok (some (.digests #[hashRecord hi.1])),
  ask "ACCEPT_VIEW b3 with every boundary entry kept (catch-up mode, the rule of protocol 3)"
    (.acceptView "b3" alice false false (strayOlder.map toView).toArray #[]) .ok
    (some (.viewed #[.known (hashRecord older.1)])),
  ask "HEADS b3: older is a head no record links (the round-2 stray head)" (.heads "b3") .ok
    (some (.digests (sorted #[hashRecord hi.1, hashRecord older.1]))),
  ask "ACCEPT lateC at Alice" (.accept "s" (.ofRec lateC.1) lateC.2) .ok,
  ask "HEADS s: hi and lateC" (.heads "s") .ok
    (some (.digests (sorted #[hashRecord hi.1, hashRecord lateC.1]))),
  ask "ACCEPT lateC at Bob, with its opening: missing older"
    (.accept "b" (.ofRec lateC.1) lateC.2) .missing
    (some (.accept lateC.1 (.missing #[hashRecord older.1]))),
  ask "SERVE per-digest to bob, asking for older again: older as a digest only"
    (.serve "s" (serveFrom bob keyBob (wanted := some #[hashRecord older.1])
      (records := strayRecords.push lateC))) .ok
    (some (.served ⟨bob, Serve.keyTag keyBob, rid⟩ strayOlder)),
  ask "ACCEPT_VIEW b, per-digest mode, the reply and lateC as pending: both taken"
    (.acceptView "b" alice false true (strayOlder.map toView).toArray
      #[.addressed (encode lateC.1) true (some lateC.2)]) .ok
    (some (.viewed #[.known (hashRecord older.1), .record (.accepted (hashRecord lateC.1))])),
  ask "HEADS b: Alice's again (hi and lateC)" (.heads "b") .ok
    (some (.digests (sorted #[hashRecord hi.1, hashRecord lateC.1]))),
  ask "ADDRESSED bob in b: hi and lateC, lateC's audience recorded" (.addressed "b" bob keyBob) .ok
    (some (.digests (digestsOf [hi, lateC]))),
  ask "ACCEPT_VIEW b, per-digest mode: a pending record of another chat links the digest, but is not taken, so the digest is ignored"
    (.acceptView "b" alice false true #[.boundary (dig 0x77)] #[.after (encode foreignLinking)]) .ok
    (some (.viewed #[.code .ignored, .record .wrongChat])),
  ask "ACCEPT_VIEW b, per-digest mode: a pending record that also lacks another digest is not taken, so the digest is ignored and reported missing again"
    (.acceptView "b" alice false true #[.boundary (dig 0x78)] #[.after (encode twoUnknown)]) .ok
    (some (.viewed #[.code .ignored, .record (.missing #[dig 0x78, dig 0x79])])),
  ask "ACCEPT_VIEW b, per-digest mode: the pending record with both digests answered: all taken"
    (.acceptView "b" alice false true #[.boundary (dig 0x78), .boundary (dig 0x79)]
      #[.after (encode twoUnknown)]) .ok
    (some (.viewed #[.known (dig 0x78), .known (dig 0x79),
      .record (.accepted (hashRecord twoUnknown))])),
  ask "HEADS b: hi, lateC and the new record" (.heads "b") .ok
    (some (.digests (sorted #[hashRecord hi.1, hashRecord lateC.1, hashRecord twoUnknown])))]

/-- `2^32 - 1` as 4 bytes. -/
def ffff : ByteArray := ⟨#[0xff, 0xff, 0xff, 0xff]⟩

/-- Requests that cannot be read, and counts that no input could hold. -/
def fuzz : Array Step := #[
  raw "an empty payload" .empty .badRequest,
  raw "op 0x00" ⟨#[0x00]⟩ .unknownOp,
  raw "op 0x30" ⟨#[0x30]⟩ .unknownOp,
  raw "AUDIENCE with no body" ⟨#[0x11]⟩ .badRequest,
  raw "op 0xff with a body" ⟨#[0xff, 1, 2, 3]⟩ .unknownOp,
  raw "VERSION with a byte left over" ⟨#[0x01, 0x00]⟩ .badRequest,
  raw "NEW with the group cut short" ((Request.new "c" group).write.extract 0 20) .badRequest,
  raw "NEW with a byte left over" ((Request.new "c" group).write.push 0) .badRequest,
  raw "NEW with a chat key that is not UTF-8"
    (Write.u8 0x02 ++ Write.bytes ⟨#[0xff]⟩ ++ group.bytes) .badRequest,
  raw "HEADS with a chat key length of 2^32 - 1" (Write.u8 0x08 ++ ffff) .badRequest,
  raw "HASH whose link count is 2^32 - 1, with no links after it"
    (Write.u8 0x06 ++ group.bytes ++ (dig 0xc0).bytes ++ ffff ++ alice.bytes) .badRequest,
  raw "ACCEPT whose link count is 2^32 - 1"
    (Write.u8 0x07 ++ Write.str "c" ++ group.bytes ++ (dig 0xc0).bytes ++ ffff ++ alice.bytes)
    .badRequest,
  raw "OPEN with form byte 2" (Write.u8 0x03 ++ Write.str "c" ++ group.bytes ++ Write.u8 2)
    .badRequest,
  raw "OPEN a list whose record count is 2^32 - 1, with nothing after it"
    (Write.u8 0x03 ++ Write.str "c" ++ group.bytes ++ Write.u8 1 ++ ffff) .badRequest,
  raw "OPEN a blob whose length field is 2^32 - 1"
    (Write.u8 0x03 ++ Write.str "c" ++ group.bytes ++ Write.u8 0 ++ ffff) .badRequest,
  ask "OPEN a blob whose header claims 2^32 - 1 records: too large, before any record is read"
    (.open "c" group (.blob (s3 hugeCountBlob))) .tooLarge,
  ask "SALVAGE the same blob" (.salvage "c" group (.blob (s3 hugeCountBlob))) .tooLarge,
  ask "OPEN a blob whose header claims 2^24 records: too large"
    (.open "c" group (.blob (s3 (blobTag ++ group.bytes ++ u32be (2^24))))) .tooLarge,
  ask "OPEN a blob of another group whose header claims 2^24 records: too large first"
    (.open "c" group (.blob (s3 (blobTag ++ otherGroup.bytes ++ u32be (2^24))))) .tooLarge,
  ask "OPEN a blob whose header claims 2^24 - 1 records and holds none: malformed"
    (.open "c" group (.blob (s3 (blobTag ++ group.bytes ++ u32be (2^24 - 1))))) .malformed,
  raw "COMMIT with the nonce cut short" (Write.u8 0x05 ++ group.bytes ++ alice.bytes ++
    ⟨Array.replicate 31 0x4e⟩) .badRequest,
  raw "COMMIT whose DataMessage length is past the end"
    (Write.u8 0x05 ++ group.bytes ++ alice.bytes ++ nonce.bytes ++ ffff) .badRequest,
  ask "COMMIT a DataMessage field whose length is past the end"
    (.commit group alice nonce (bytesOf [0x0a, 0xff, 0xff, 0xff, 0xff, 0x0f, 0x41])) .malformed,
  ask "NEW c (for the requests below)" (.new "c" group) .ok,
  raw "REACH_SET whose count is 2^32 - 1" (Write.u8 0x0B ++ Write.str "c" ++ ffff) .badRequest,
  raw "CLASSIFY whose fact count is 2^32 - 1" (Write.u8 0x0D ++ Write.str "c" ++ ffff)
    .badRequest,
  raw "CLASSIFY with provenance byte 3" (Write.u8 0x0D ++ Write.str "c" ++ u32be 1 ++
    (dig 1).bytes ++ Write.u8 3 ++ u32be 0) .badRequest,
  raw "CLASSIFY with a disown count of 2^32 - 1" (Write.u8 0x0D ++ Write.str "c" ++ u32be 1 ++
    (dig 1).bytes ++ Write.u8 0 ++ ffff) .badRequest,
  raw "MERGE whose blob length is 2^32 - 1" (Write.u8 0x0C ++ Write.str "c" ++ ffff) .badRequest,
  ask "MERGE a blob whose header claims 2^32 - 1 records: too large" (.merge "c" (s3 hugeCountBlob))
    .tooLarge,
  raw "ACCEPT_RECORD with opening flag 2" (Write.u8 0x10 ++ Write.str "c" ++
    Write.bytes (encode a1) ++ Write.u8 2) .badRequest,
  raw "ACCEPT_RECORD with no opening flag" (Write.u8 0x10 ++ Write.str "c" ++
    Write.bytes (encode a1)) .badRequest,
  raw "ACCEPT_RECORD with a byte left over"
    ((Request.acceptRecord "c" (encode a1) none).write.push 0) .badRequest,
  raw "ACCEPT_RECORD whose opening length is 2^32 - 1" (Write.u8 0x10 ++ Write.str "c" ++
    Write.bytes (encode a1) ++ Write.u8 1 ++ ffff) .badRequest,
  raw "GET with the digest cut short" (Write.u8 0x0A ++ Write.str "c" ++ ⟨Array.replicate 31 1⟩)
    .badRequest,
  raw "ACCEPT with no opening" (Write.u8 0x07 ++ Write.str "c" ++ Write.parts (.ofRec a1))
    .badRequest,
  raw "ACCEPT whose opening length is 2^32 - 1" (Write.u8 0x07 ++ Write.str "c" ++
    Write.parts (.ofRec a1) ++ ffff) .badRequest,
  raw "ACCEPT with the opening flag of protocol 3 (0: none)" (Write.u8 0x07 ++ Write.str "c" ++
    Write.parts (.ofRec a1) ++ Write.u8 0) .badRequest,
  raw "AUDIENCE whose member count is 2^32 - 1" (Write.u8 0x11 ++ ffff) .badRequest,
  raw "AUDIENCE with key flag 2" (Write.u8 0x11 ++ u32be 1 ++ alice.bytes ++ Write.u8 2)
    .badRequest,
  raw "AUDIENCE with a key cut short" (Write.u8 0x11 ++ u32be 1 ++ alice.bytes ++ Write.u8 1 ++
    keyAlice.extract 0 32) .badRequest,
  raw "ADDRESSED with a key cut short" (Write.u8 0x13 ++ Write.str "c" ++ bob.bytes ++
    keyBob.extract 0 32) .badRequest,
  raw "SERVE with a key cut short" ((Request.serve "c" (serveFrom bob keyBob)).write.extract 0 60)
    .badRequest,
  raw "SERVE with mode byte 2" (Write.u8 0x12 ++ Write.str "c" ++ alice.bytes ++ bob.bytes ++
    keyBob ++ rid ++ u32be 0 ++ u32be 0 ++ Write.u8 2) .badRequest,
  raw "SERVE with export flag 2" (Write.u8 0x12 ++ Write.str "c" ++ alice.bytes ++ bob.bytes ++
    keyBob ++ rid ++ u32be 0 ++ u32be 0 ++ Write.u8 0 ++ Write.u8 2) .badRequest,
  raw "SERVE whose held count is 2^32 - 1" (Write.u8 0x12 ++ Write.str "c" ++ alice.bytes ++
    bob.bytes ++ keyBob ++ rid ++ u32be 0 ++ u32be 0 ++ Write.u8 0 ++ Write.u8 0 ++ Write.u8 0 ++
    u32be 0 ++ u32be 0 ++ ffff) .badRequest,
  raw "SERVE with a byte left over" ((Request.serve "c" (serveFrom bob keyBob)).write.push 0)
    .badRequest,
  ask "SERVE in c: the store is empty, so no entries" (.serve "c" (serveFrom bob keyBob)) .ok
    (some (.served ⟨bob, Serve.keyTag keyBob, rid⟩ [])),
  raw "ACCEPT_VIEW with entry kind 3" (Write.u8 0x14 ++ Write.str "c" ++ alice.bytes ++
    Write.u8 0 ++ Write.u8 0 ++ u32be 1 ++ Write.u8 3 ++ u32be 0) .badRequest,
  raw "ACCEPT_VIEW with import flag 2" (Write.u8 0x14 ++ Write.str "c" ++ alice.bytes ++
    Write.u8 2 ++ Write.u8 0 ++ u32be 0 ++ u32be 0) .badRequest,
  raw "ACCEPT_VIEW with mode byte 2" (Write.u8 0x14 ++ Write.str "c" ++ alice.bytes ++
    Write.u8 0 ++ Write.u8 2 ++ u32be 0 ++ u32be 0) .badRequest,
  raw "ACCEPT_VIEW without a mode byte (the layout of protocol 3)" (Write.u8 0x14 ++
    Write.str "c" ++ alice.bytes ++ Write.u8 0 ++ u32be 0) .badRequest,
  raw "ACCEPT_VIEW without a pending list" (Write.u8 0x14 ++ Write.str "c" ++ alice.bytes ++
    Write.u8 0 ++ Write.u8 1 ++ u32be 0) .badRequest,
  raw "ACCEPT_VIEW whose entry count is 2^32 - 1" (Write.u8 0x14 ++ Write.str "c" ++
    alice.bytes ++ Write.u8 0 ++ Write.u8 0 ++ ffff) .badRequest,
  raw "ACCEPT_VIEW whose pending count is 2^32 - 1" (Write.u8 0x14 ++ Write.str "c" ++
    alice.bytes ++ Write.u8 0 ++ Write.u8 1 ++ u32be 0 ++ ffff) .badRequest,
  raw "ACCEPT_VIEW with a boundary digest cut short" (Write.u8 0x14 ++ Write.str "c" ++
    alice.bytes ++ Write.u8 0 ++ Write.u8 0 ++ u32be 1 ++ Write.u8 2 ++
    ⟨Array.replicate 31 1⟩ ++ u32be 0) .badRequest,
  raw "LINKABLE whose count is 2^32 - 1" (Write.u8 0x15 ++ Write.str "c" ++ ffff) .badRequest,
  raw "NEW_RELATIVE with the group cut short" ((Request.newRelative "r" group).write.extract 0 20)
    .badRequest,
  ask "HEADS c: the store is still empty" (.heads "c") .ok (some (.digests #[]))]

/-! ## Protocol-5 sessions (docs/apps/BUILD_M1.md §E)

Each lane's sessions, and the protocol-5 statuses its sessions do not produce yet (`uncovered`:
the lane empties its list as its sessions cover them; all three lists are empty at
integration). -/

-- [BEGIN lane base] sessions
/-- Lane base's sessions (`pieces`: `CHANNEL`, `PIECES_BIND`, `PIECE_ACCEPT`, `PIECE_OPENING`,
`PIECES_COMPLETE`, `ASSEMBLE`, the piece-key guard, and the torrent beat's repair at the frame
level). -/
def baseSessions : Array (String × Array Step) := #[]

/-- Lane base's statuses that no session produces yet. -/
def baseUncovered : List Code := [.badPiece, .badApp]
-- [END lane base]

-- [BEGIN lane torrent] sessions
/-- Lane torrent's sessions (`torrent`: `BT_BUILD`, `BT_FILE`, and the torrent beat end to end). -/
def torrentSessions : Array (String × Array Step) := #[]

/-- Lane torrent's statuses that no session produces yet. -/
def torrentUncovered : List Code := [.badName]
-- [END lane torrent]

-- [BEGIN lane git] sessions
/-- Lane git's sessions (`git`: `GIT_PREPARE`, `GIT_OBJECTS`, `GIT_VIEW`, and the git beat: P1,
forced P2, equal views, `GATE`, the share S, P3, and `ROOT`). -/
def gitSessions : Array (String × Array Step) := #[]

/-- Lane git's statuses that no session produces yet. -/
def gitUncovered : List Code := [.pushRefused, .badObjects, .openingsMissing]
-- [END lane git]

/-- The sessions, each run on a fresh `zrdtd`: protocol 4's, then each lane's. -/
def sessions : Array (String × Array Step) :=
  #[("tour", tour), ("tooLarge", tooLargeSteps), ("acceptRecord", acceptRecordSteps),
    ("join", joinSteps), ("view", viewSteps), ("boundary", boundarySteps), ("fuzz", fuzz)] ++
    baseSessions ++ torrentSessions ++ gitSessions

/-- The replies of a session's steps, from the protocol-5 dispatcher `zrdtd` runs; `build` is the
build text of `VERSION`. -/
def replies (steps : Array Step) (build : String := Apps.buildId) : List ByteArray :=
  Apps.session (steps.map (·.request)).toList build

/-- Whether every step of a session gets its status, and its whole reply where one is pinned. -/
def sessionOk (steps : Array Step) : Bool :=
  (steps.toList.zip (replies steps)).all fun (s, r) =>
    r[0]? == some s.expect.byte && s.reply?.all (· == r)

#guard sessions.all fun (_, steps) => sessionOk steps

/-- The steps that fail their check, by name (empty when all pass). -/
def failures : List String :=
  sessions.toList.flatMap fun (_, steps) =>
    ((steps.toList.zip (replies steps)).filter fun (s, r) =>
      !(r[0]? == some s.expect.byte && s.reply?.all (· == r))).map (·.1.name)

-- Every op appears in some session.
#guard (List.range opNames.size).all fun i =>
  sessions.any fun (_, steps) => steps.any fun s => s.request[0]? == some (i + 1).toUInt8

-- Every status except `COLLISION` appears in some session: as the status of a reply, or for
-- `EPHEMERAL` and `IGNORED`, as the result of an `ACCEPT_VIEW` entry. Protocol-5 statuses a lane
-- has not covered yet are listed in its `uncovered` list.
#guard (Code.all.filter (· ∉ [.collision, .ephemeral, .ignored] ++ baseUncovered ++
    torrentUncovered ++ gitUncovered)).all fun c =>
  sessions.any fun (_, steps) => steps.any (·.expect == c)
#guard (baseUncovered ++ torrentUncovered ++ gitUncovered).all (· ∈ Code.v5)

-- [BEGIN lane base] checks
-- Every base op appears in some session.
#guard baseOpNames.all fun (b, _) => sessions.any fun (_, steps) => steps.any (·.request[0]? == some b)
-- [END lane base]

-- [BEGIN lane torrent] checks
-- Every torrent op appears in some session.
#guard torrentOpNames.all fun (b, _) =>
  sessions.any fun (_, steps) => steps.any (·.request[0]? == some b)
-- [END lane torrent]

-- [BEGIN lane git] checks
-- Every git op appears in some session.
#guard gitOpNames.all fun (b, _) => sessions.any fun (_, steps) => steps.any (·.request[0]? == some b)
-- [END lane git]
#guard [Code.ephemeral, .ignored].all fun c =>
  (replies viewSteps).any fun r => r[0]? == some 0 && containsBytes r c.write

/-- The `sessions` section, for a `zrdtd` whose build text is `build`. -/
def sessionsJson (build : String) : Json :=
  .arr <| sessions.map fun (name, steps) =>
    .obj #[("name", .str name), ("steps", .arr <|
      (steps.toList.zip (replies steps build)).toArray.map
      fun (s, r) =>
        .obj (#[("name", .str s.name), ("op", .str (opName s.request)),
          ("status", .str s.expect.name), ("request", hex s.request), ("reply", hex r)] ++
          (if s.buildDependent then #[("buildDependent", .bool true)] else #[])))]
where
  /-- The name of a request's op, or `none` for an op byte that has no name. -/
  opName (b : ByteArray) : String :=
    match b[0]? with
    | some x => (Proto.opName? x).getD s!"0x{hexOfBytes ⟨#[x]⟩}"
    | none => "(empty)"

/-! ## Replies no request can produce -/

/-- `COLLISION` replies (a SHA-256 collision would be needed to get them from a request). -/
def collisionReplies : Json :=
  .arr #[
    .obj #[("name", .str "ACCEPT: COLLISION at digest a1"),
      ("reply", hex (Reply.accept a1 (.collision (hashRecord a1))).write)],
    .obj #[("name", .str "OPEN or MERGE: COLLISION at digest a1"),
      ("reply", hex (Reply.opened (.error (.collision (hashRecord a1)))).write)],
    .obj #[("name", .str "SALVAGE: COLLISION at digest a1"),
      ("reply", hex (Reply.salvaged (.error (.collision (hashRecord a1)))).write)]]

/-! ## The file -/

/-- All of `vectors/vectors.json`, for a `zrdtd` whose build text is `build`. -/
def vectors (build : String) : Json :=
  .obj #[
    ("about", .str ("Generated by core/Zrdt/Vectors.lean (make vectors); do not edit. " ++
      "Byte layouts: core/Zrdt/Proto.lean (frames, requests, replies) and core/Zrdt/Encode.lean " ++
      "(records, blobs). All bytes are lower-case hex. Run each session on a fresh zrdtd: send " ++
      "u32 length (big-endian) + request, read u32 length + reply, compare the reply.")),
    ("protocol", .num protocolVersion),
    ("build", .str build),
    ("sha256", shaJson),
    ("records", recordsJson),
    ("recordDecode", recordDecodeJson),
    ("blobs", blobsJson),
    ("blobDecode", blobDecodeJson),
    ("commit", commitJson),
    ("keyTag", keyTagJson),
    ("replies", collisionReplies),
    ("sessions", sessionsJson build)]

end Zrdt.Vectors
