import Zrdt.Proto

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
- `blobs`: store blobs;
- `commit`: `DataMessage` bytes, the bytes the commitment covers, the commitment and the opening
  (`null` where the message is malformed), including messages with fields 15 and 200;
- `replies`: reply bytes that no request can produce here (`COLLISION` needs two records with the
  same SHA-256);
- `sessions`: request and reply payloads. Run each session on a fresh `zrdtd`, in order: send
  `length (u32) ‖ request`, read `length (u32) ‖ reply`, and compare the reply. Every op and every
  reply of every op appears, except `COLLISION`. The `fuzz` session holds unreadable requests and
  counts no input could hold. A step marked `buildDependent` (`VERSION`) contains the build text:
  another build of `zrdtd` gives other bytes there. The file's `build` is the text of the
  `zrdtd` built from the same sources.

Each step states the status it must get; the `#guard`s below check them, and pin some reply
bodies, when this file is built.
-/

namespace Zrdt.Vectors

open Proto Examples

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

/-- Example `DataMessage` bytes (fields from `Zrdt.Commit`'s examples). -/
def commitCases : Array (String × ByteArray) :=
  #[("body, groupV2 (15), timestamp, zrdt (200), unknown field 99", dataMessage),
    ("the same without fields 15 and 200 (the opening)",
      bodyField ++ timestampField ++ unknownField),
    ("empty", .empty),
    ("field 15 twice, around the body", groupV2Field ++ bodyField ++ groupV2Field),
    ("field 15 with a longer form of its key (fa 00)", bytesOf [0xfa, 0x00, 0] ++ bodyField),
    ("field 200 only", zrdtField),
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
      ("opening", ((commitWithOpening group alice nonce m).map (hex ·.2)).getD .null)]

-- The opening has the same commitment as the full message; malformed messages have none.
#guard (commitCases.map fun (_, m) => (commit group alice nonce m).isSome) ==
  #[true, true, true, true, true, true, false, false, false, false, false]
#guard commit group alice nonce commitCases[0]!.2 == commit group alice nonce commitCases[1]!.2

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

/-- Alice's message `dataMessage` (`Zrdt.Commit`): its commitment and its opening. -/
def m1Opened : Digest × ByteArray :=
  (commitWithOpening group alice nonce dataMessage).getD (Digest.zero, .empty)

/-- The `COMMIT` reply for `dataMessage`. -/
def m1Committed : Reply := .committed m1Opened.1 m1Opened.2

/-- A record of Alice's whose commit is the real commitment of `dataMessage`. It links `a1`. -/
def m1 : Rec := Rec.make group m1Opened.1 #[hashRecord a1] alice

/-- The same commit and links in Bob's name: Alice's opening does not belong to it. -/
def m1AsBob : Rec := Rec.make group m1Opened.1 #[hashRecord a1] bob

#guard openingMatches group alice m1.commit m1Opened.2 && m1Opened.2.size == 32 + 20

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
  ask "ACCEPT a1: its digest and encoding" (.accept "camping" (.ofRec a1)) .ok
    (some (.accept a1 (.accepted (hashRecord a1)))),
  ask "ACCEPT a1 again: accepted, nothing changes" (.accept "camping" (.ofRec a1)) .ok
    (some (.accept a1 (.accepted (hashRecord a1)))),
  ask "ACCEPT a2 before b1 and c1: missing both, sorted" (.accept "camping" (.ofRec a2))
    .missing (some (.accept a2 (.missing (sorted #[hashRecord b1, hashRecord c1])))),
  ask "HEADS: a1" (.heads "camping") .ok (some (.digests #[hashRecord a1])),
  ask "ACCEPT b1" (.accept "camping" (.ofRec b1)) .ok,
  ask "ACCEPT c1, its link given twice: the canonical encoding comes back" (.accept "camping"
    ⟨group, dig 0xc1, #[hashRecord a1, hashRecord a1], carol⟩) .ok
    (some (.accept c1 (.accepted (hashRecord c1)))),
  ask "HEADS: b1 and c1, sorted" (.heads "camping") .ok
    (some (.digests (sorted #[hashRecord b1, hashRecord c1]))),
  ask "ACCEPT a2" (.accept "camping" (.ofRec a2)) .ok,
  ask "ACCEPT a record of another group: wrong chat" (.accept "camping" (.ofRec foreign))
    .wrongChat,
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
  ask "COMMIT a DataMessage with fields 15 and 200: the commitment and the opening"
    (.commit group alice nonce dataMessage) .ok (some m1Committed),
  ask "COMMIT the opening's bytes (fields 15 and 200 already removed): the same reply"
    (.commit group alice nonce (bodyField ++ timestampField ++ unknownField)) .ok
    (some m1Committed),
  ask "COMMIT a malformed DataMessage" (.commit group alice nonce (bodyField ++ bytesOf [0x0b]))
    .malformed,
  ask "ENCODE camping (a1 b1 c1 a2)" (.encode "camping") .ok (some (.blob all4.encode)),
  ask "ACCEPT f1 (a fake in Bob's name)" (.accept "camping" (.ofRec f1)) .ok,
  ask "ACCEPT a3" (.accept "camping" (.ofRec a3)) .ok,
  ask "ACCEPT b2" (.accept "camping" (.ofRec b2)) .ok,
  ask "ACCEPT c2" (.accept "camping" (.ofRec c2)) .ok,
  ask "CLASSIFY: a3, b2 live (b2 disowns f1), c2 relayed, f1 imported"
    (.classify "camping" tourFacts) .ok (some (.classified tourStatuses)),
  ask "CLASSIFY with no facts: all unconfirmed" (.classify "camping" #[]) .ok
    (some (.classified (tourStatuses.map fun (d, _) => (d, .unconfirmed)))),
  ask "OPEN copy from a blob" (.open "copy" group (.blob all4.encode)) .ok,
  ask "HEADS of copy: a2" (.heads "copy") .ok (some (.digests #[hashRecord a2])),
  ask "OPEN copy again: already open" (.open "copy" group (.blob all4.encode)) .chatOpen,
  ask "OPEN list from records in any order" (.open "list" group
    (.records #[encode a2, encode c1, encode b1, encode a1])) .ok,
  ask "ENCODE list: the same blob as camping had" (.encode "list") .ok (some (.blob all4.encode)),
  ask "OPEN rev from a blob with the records in reverse digest order" (.open "rev" group
    (.blob (encodeBlob group all4.records.reverse))) .ok,
  ask "ENCODE rev: the records sorted by digest" (.encode "rev") .ok (some (.blob all4.encode)),
  ask "OPEN rep from a blob that holds b1 twice" (.open "rep" group
    (.blob (encodeBlob group #[a1, b1, c1, b1, a2]))) .ok,
  ask "ENCODE rep: b1 counts once" (.encode "rep") .ok (some (.blob all4.encode)),
  ask "OPEN rep2 from a record list that holds a1 twice" (.open "rep2" group
    (.records #[encode a2, encode a1, encode c1, encode b1, encode a1])) .ok,
  ask "ENCODE rep2: a1 counts once" (.encode "rep2") .ok (some (.blob all4.encode)),
  ask "OPEN a doctored blob (b1 cut out): unverifiable a2, missing b1"
    (.open "bad" group (.blob (encodeBlob group #[a1, c1, a2]))) .unverifiable
    (some (.opened (.error (.unverifiable #[hashRecord a2] #[hashRecord b1])))),
  ask "HEADS bad: nothing was loaded" (.heads "bad") .noChat,
  ask "OPEN bytes that are not a blob" (.open "bad" group (.blob "junk".toUTF8)) .malformed,
  ask "OPEN a blob of another group" (.open "bad" group (.blob (encodeBlob otherGroup #[])))
    .wrongChat,
  ask "OPEN a list with a record of another group" (.open "bad" group
    (.records #[encode a1, encode foreign])) .wrongChat,
  ask "OPEN a list with a record that does not decode" (.open "bad" group badList) .malformed,
  ask "SALVAGE the doctored blob: dropped a2, missing b1" (.salvage "kept" group
    (.blob (encodeBlob group #[a1, c1, a2]))) .ok
    (some (.salvaged (.ok (#[hashRecord a2], #[hashRecord b1])))),
  ask "HEADS kept: c1" (.heads "kept") .ok (some (.digests #[hashRecord c1])),
  ask "SALVAGE kept again: already open" (.salvage "kept" group (.blob all4.encode)) .chatOpen,
  ask "SALVAGE the doctored blob with a2 twice: a2 dropped once" (.salvage "kept3" group
    (.blob (encodeBlob group #[a2, a1, c1, a2]))) .ok
    (some (.salvaged (.ok (#[hashRecord a2], #[hashRecord b1])))),
  ask "SALVAGE a list: nothing to drop" (.salvage "kept2" group
    (.records #[encode c1, encode a1])) .ok (some (.salvaged (.ok (#[], #[])))),
  ask "SALVAGE bytes that are not a blob" (.salvage "bad" group (.blob "junk".toUTF8)) .malformed,
  ask "SALVAGE a blob of another group" (.salvage "bad" group (.blob (encodeBlob otherGroup #[])))
    .wrongChat,
  ask "SALVAGE a list with a record that does not decode" (.salvage "bad" group badList)
    .malformed,
  ask "MERGE the doctored blob into kept: unverifiable, kept unchanged"
    (.merge "kept" (encodeBlob group #[a1, c1, a2])) .unverifiable,
  ask "MERGE a blob of another group: wrong chat" (.merge "kept" (encodeBlob otherGroup #[]))
    .wrongChat,
  ask "MERGE bytes that are not a blob" (.merge "kept" "junk".toUTF8) .malformed,
  ask "HEADS kept: still c1" (.heads "kept") .ok (some (.digests #[hashRecord c1])),
  ask "MERGE a1 b1 into kept" (.merge "kept" storeAB.encode) .ok,
  ask "HEADS kept: b1 and c1" (.heads "kept") .ok
    (some (.digests (sorted #[hashRecord b1, hashRecord c1]))),
  ask "MERGE into a chat that is not open" (.merge "nochat" storeAB.encode) .noChat,
  ask "ACCEPT into a chat that is not open" (.accept "nochat" (.ofRec a1)) .noChat,
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
  ask "ACCEPT a record with 4097 links" (.accept "big" (.ofRec tooManyLinks)) .tooLarge,
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
  ask "HEADS r: still m1" (.heads "r") .ok (some (.digests #[hashRecord m1]))]

/-- `2^32 - 1` as 4 bytes. -/
def ffff : ByteArray := ⟨#[0xff, 0xff, 0xff, 0xff]⟩

/-- Requests that cannot be read, and counts that no input could hold. -/
def fuzz : Array Step := #[
  raw "an empty payload" .empty .badRequest,
  raw "op 0x00" ⟨#[0x00]⟩ .unknownOp,
  raw "op 0x11" ⟨#[0x11]⟩ .unknownOp,
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
    (.open "c" group (.blob hugeCountBlob)) .tooLarge,
  ask "SALVAGE the same blob" (.salvage "c" group (.blob hugeCountBlob)) .tooLarge,
  ask "OPEN a blob whose header claims 2^24 records: too large"
    (.open "c" group (.blob (blobTag ++ group.bytes ++ u32be (2^24)))) .tooLarge,
  ask "OPEN a blob of another group whose header claims 2^24 records: too large first"
    (.open "c" group (.blob (blobTag ++ otherGroup.bytes ++ u32be (2^24)))) .tooLarge,
  ask "OPEN a blob whose header claims 2^24 - 1 records and holds none: malformed"
    (.open "c" group (.blob (blobTag ++ group.bytes ++ u32be (2^24 - 1)))) .malformed,
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
  ask "MERGE a blob whose header claims 2^32 - 1 records: too large" (.merge "c" hugeCountBlob)
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
  ask "HEADS c: the store is still empty" (.heads "c") .ok (some (.digests #[]))]

/-- The sessions, each run on a fresh `zrdtd`. -/
def sessions : Array (String × Array Step) :=
  #[("tour", tour), ("tooLarge", tooLargeSteps), ("acceptRecord", acceptRecordSteps),
    ("fuzz", fuzz)]

/-- The replies of a session's steps; `build` is the build text of `VERSION`. -/
def replies (steps : Array Step) (build : String := buildId) : List ByteArray :=
  session (steps.map (·.request)).toList build

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
#guard (List.range 16).all fun i =>
  sessions.any fun (_, steps) => steps.any fun s => s.request[0]? == some (i + 1).toUInt8

-- Every status except `COLLISION` appears in some session.
#guard (Code.all.filter (· != .collision)).all fun c =>
  sessions.any fun (_, steps) => steps.any (·.expect == c)

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
    ("replies", collisionReplies),
    ("sessions", sessionsJson build)]

end Zrdt.Vectors
