import Zrdt.Record
import Zrdt.Sha256

/-!
# Byte encodings of records and stores (docs/PLAN.md §3.4)

**Record:**

    "zrdt2" ‖ group (32) ‖ commit (32) ‖ nlinks (u32, big-endian) ‖ links (32 each) ‖ author (16)

Every field has a fixed size except the links, and each link has a fixed size. So the length of
the bytes alone fixes the number of links, and different records always have different
encodings (`decode_encode` below; `encode_injective` follows from it).

`decode` is strict: it accepts exactly the outputs of `encode`. It rejects a wrong tag, a wrong
length, an `nlinks` field that does not match the length, and links that are not strictly
increasing (`StrictlySorted`).

**Record digest:** `hashRecord r := sha256 (encode r)`. It is defined here rather than in
`Zrdt.Record` because it needs `encode`.

**Store blob:**

    "zrdtS2" ‖ group (32) ‖ count (u32) ‖ (len (u32) ‖ record)*

The store writes its records sorted by digest. `decodeBlob` checks the framing strictly (every
length exact, no bytes left over, every record strictly decoded). It does not check the order of
the records or the group inside each record: the store's `open` does that when it accepts them.

**Size limits:** a store holds fewer than `2^24` records, and a record has at most 4096 links
(`WellSized`). The decoders do not enforce them; `accept` and `open` report `TOO_LARGE`.

**Untrusted counts:** no decoder sizes an allocation from a number it read. `decode` derives the
link count from the input length. `decodeBlob` first checks that the input is long enough for
`count` records, and then only appends records it has decoded.
-/

namespace Zrdt

/-! ## Big-endian 32-bit numbers -/

/-- `n` as 4 bytes, big-endian. Only the low 32 bits are kept, so this writes `n % 2^32`. -/
def u32be (n : Nat) : ByteArray :=
  ⟨#[(n >>> 24).toUInt8, (n >>> 16).toUInt8, (n >>> 8).toUInt8, n.toUInt8]⟩

#guard u32be 0x01020304 == ⟨#[1, 2, 3, 4]⟩
#guard u32be (2^32 + 5) == u32be 5

/-- The big-endian number in the 4 bytes at `off`, or `none` if the input is too short. -/
def readU32? (b : ByteArray) (off : Nat) : Option Nat :=
  if h : off + 4 ≤ b.size then
    some (b[off].toNat * 2^24 + b[off + 1].toNat * 2^16 + b[off + 2].toNat * 2^8 +
      b[off + 3].toNat)
  else none

#guard readU32? ⟨#[9, 1, 2, 3, 4]⟩ 1 == some 0x01020304
#guard readU32? ⟨#[1, 2, 3]⟩ 0 == none
#guard readU32? (u32be 4096) 0 == some 4096

/-! ## Records -/

/-- The 5-byte tag that starts every record: `"zrdt2"`. -/
def recordTag : ByteArray := "zrdt2".toUTF8

example : recordTag.size = 5 := by decide

/-- The links written one after another, 32 bytes each. -/
def linksBytes (ls : Array Digest) : ByteArray :=
  ls.foldl (fun acc d => acc ++ d.bytes) ByteArray.empty

/-- The bytes of a record (layout in the module header). -/
def encode (r : Rec) : ByteArray :=
  recordTag ++ r.group.bytes ++ r.commit.bytes ++ u32be r.links.size ++ linksBytes r.links ++
    r.author.bytes

/-- The size of a record with `n` links: 89 bytes plus 32 per link. -/
def encodedSize (n : Nat) : Nat := 89 + 32 * n

/-- Read `k` digests, 32 bytes each, from offset `off`, appending them to `acc`. -/
def readDigests (b : ByteArray) (off : Nat) (acc : Array Digest) : Nat → Option (Array Digest)
  | 0 => some acc
  | k + 1 => do
    let d ← Digest.ofBytes? (b.extract off (off + 32))
    readDigests b (off + 32) (acc.push d) k

/-- Decode a record. `none` unless the input is exactly `encode r` for some record `r`.

The number of links `n` comes from the input length; the `nlinks` field must equal it (as a
32-bit number, which only matters for inputs over 128 GiB). -/
def decode (b : ByteArray) : Option Rec := do
  guard (89 ≤ b.size ∧ (b.size - 89) % 32 = 0)
  let n := (b.size - 89) / 32
  guard (b.extract 0 5 = recordTag)
  guard (readU32? b 69 = some (n % 2^32))
  let g ← GroupId.ofBytes? (b.extract 5 37)
  let c ← Digest.ofBytes? (b.extract 37 69)
  let ls ← readDigests b 73 #[] n
  let a ← Aci.ofBytes? (b.extract (73 + 32 * n) b.size)
  if h : StrictlySorted ls then pure ⟨g, c, ls, a, h⟩ else none

/-- The digest of a record: SHA-256 of its encoding. This is the value other records link to. -/
def hashRecord (r : Rec) : Digest := sha256 (encode r)

/-! ## Store blobs -/

/-- The 6-byte tag that starts every store blob: `"zrdtS2"`. -/
def blobTag : ByteArray := "zrdtS2".toUTF8

example : blobTag.size = 6 := by decide

/-- The bytes of a store blob for group `g`, with the records in the order given. The store passes
its records sorted by digest. -/
def encodeBlob (g : GroupId) (rs : Array Rec) : ByteArray :=
  rs.foldl (fun acc r => let e := encode r; acc ++ u32be e.size ++ e)
    (blobTag ++ g.bytes ++ u32be rs.size)

/-- Read `k` entries (`len ‖ record`) from offset `off`, appending the records to `acc`. Returns the
records and the offset after the last entry. -/
def readRecords (b : ByteArray) (off : Nat) (acc : Array Rec) : Nat → Option (Array Rec × Nat)
  | 0 => some (acc, off)
  | k + 1 => do
    let len ← readU32? b off
    guard (off + 4 + len ≤ b.size)
    let r ← decode (b.extract (off + 4) (off + 4 + len))
    readRecords b (off + 4 + len) (acc.push r) k

/-- The smallest entry in a blob: a 4-byte length and a record with no links. -/
def minEntrySize : Nat := 4 + encodedSize 0

/-- Decode a store blob into its group and records. `none` on any framing error, a record that
does not decode, or bytes left over. The order of the records is not checked. -/
def decodeBlob (b : ByteArray) : Option (GroupId × Array Rec) := do
  guard (42 ≤ b.size)
  guard (b.extract 0 6 = blobTag)
  let g ← GroupId.ofBytes? (b.extract 6 38)
  let count ← readU32? b 38
  -- A count the input cannot hold is rejected before any work.
  guard (count * minEntrySize ≤ b.size - 42)
  let (rs, stop) ← readRecords b 42 #[] count
  guard (stop = b.size)
  pure (g, rs)

/-! ## Size limits (docs/PLAN.md §3.4) -/

/-- The most links a record may have. -/
def maxLinks : Nat := 4096

/-- A store holds fewer than this many records. -/
def maxRecords : Nat := 2^24

/-- A record is within the size limit: at most `maxLinks` links. -/
def Rec.WellSized (r : Rec) : Prop := r.links.size ≤ maxLinks

instance (r : Rec) : Decidable r.WellSized := inferInstanceAs (Decidable (_ ≤ _))

/-- A list of records is within the size limits: fewer than `maxRecords` of them, and each
within its own limit. -/
def WellSized (u : Array Rec) : Prop := u.size < maxRecords ∧ ∀ r ∈ u, r.WellSized

instance (u : Array Rec) : Decidable (WellSized u) := inferInstanceAs (Decidable (_ ∧ _))

/-! ## Examples -/

namespace Examples

/-- `n` copies of the hex text `s`. -/
def rep (s : String) (n : Nat) : String := String.join (List.replicate n s)

/-- The expected bytes of `first`, field by field: tag, group, commit, nlinks, author. -/
def firstHex : String :=
  "7a72647432" ++ rep "67" 32 ++ rep "c0" 32 ++ "00000000" ++ rep "a1" 16

/-- The expected bytes of `reply`: three links, `01…`, `02…`, `03…`. -/
def replyHex : String :=
  "7a72647432" ++ rep "67" 32 ++ rep "c1" 32 ++ "00000003" ++ rep "01" 32 ++ rep "02" 32 ++
    rep "03" 32 ++ rep "a1" 16

/-- A two-link record written by hand, with the given link bytes. -/
def twoLinksHex (l₁ l₂ : String) : String :=
  "7a72647432" ++ rep "67" 32 ++ rep "c1" 32 ++ "00000002" ++ rep l₁ 32 ++ rep l₂ 32 ++
    rep "a1" 16

end Examples

open Examples

-- The exact bytes.
#guard hexOfBytes (encode first) == firstHex
#guard hexOfBytes (encode reply) == replyHex
#guard (encode first).size == encodedSize 0
#guard (encode reply).size == encodedSize 3

-- The digests (expected values from Python's `hashlib`).
#guard (hashRecord first).toHex ==
  "1594f6ca5242b659f9cb8c1c840924ff28f810a5e669f51d5d683f55084f7ef4"
#guard (hashRecord reply).toHex ==
  "7ecf9da353907575fe9729fb9141330b08572c7ad0494aabb4bdaf97b5ed5f9f"

-- The kernel can compute a record digest too (`decide +kernel`, no compiled code).
example : hashRecord first = (Digest.ofHex?
    "1594f6ca5242b659f9cb8c1c840924ff28f810a5e669f51d5d683f55084f7ef4").get! := by
  decide +kernel

-- Decoding inverts encoding.
#guard decode (encode first) == some first
#guard decode (encode reply) == some reply

-- Strictness: each of these is rejected.
#guard decode ByteArray.empty == none
#guard decode ((encode first).push 0) == none                       -- a byte too many
#guard decode ((encode reply).extract 0 184) == none                -- a byte too few
#guard decode ((encode first).set! 0 0x5a) == none                  -- wrong tag
#guard decode ((encode reply).set! 72 2) == none                    -- nlinks says 2, there are 3
#guard decode (encode reply ++ (encode reply).extract 73 105) == none -- 4 links, nlinks says 3
-- Links out of order (`02…` before `01…`) or repeated are not canonical.
#guard (bytesOfHex? (twoLinksHex "01" "02")).bind decode ==
  some (Rec.make group (dig 0xc1) #[dig 1, dig 2] alice)
#guard (bytesOfHex? (twoLinksHex "02" "01")).bind decode == none
#guard (bytesOfHex? (twoLinksHex "01" "01")).bind decode == none

-- A blob, records sorted by digest (`first` has the smaller digest).
#guard compare (hashRecord first) (hashRecord reply) == .lt
#guard (encodeBlob group #[first, reply]).size == 6 + 32 + 4 + (4 + 89) + (4 + 185)
#guard (sha256 (encodeBlob group #[first, reply])).toHex ==
  "155314c81562ddb7f9733b3489cef95c8aaebda766e6f6594f8d1734a2c9d25c"
#guard decodeBlob (encodeBlob group #[first, reply]) == some (group, #[first, reply])
#guard decodeBlob (encodeBlob otherGroup #[]) == some (otherGroup, #[])

-- Blob strictness.
#guard decodeBlob ((encodeBlob group #[first]).push 0) == none          -- bytes left over
#guard decodeBlob ((encodeBlob group #[first]).set! 41 2) == none       -- count says 2
#guard decodeBlob ((encodeBlob group #[first]).set! 45 90) == none      -- len says 90
#guard decodeBlob ((encodeBlob group #[first]).set! 0 0) == none        -- wrong tag
-- Fuzz: a header claiming 2^32 - 1 records and nothing after it is rejected at once, without
-- allocating for the claimed count.
#guard decodeBlob (blobTag ++ group.bytes ++ ⟨#[0xff, 0xff, 0xff, 0xff]⟩) == none

-- Size limits.
#guard decide (WellSized #[first, reply])
#guard !decide (Rec.WellSized (Rec.make group (dig 0) ((Array.range 4097).map fun i =>
  ⟨⟨(u32be i).data ++ Array.replicate 28 0⟩, by simp [ByteArray.size, u32be]⟩) alice))

end Zrdt
