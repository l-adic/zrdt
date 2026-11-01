import Zrdt.Record
import Zrdt.Sha256

/-!
# Byte encodings of records and stores (docs/PLAN.md §3.4)

**Record:**

    "zrdt2" ‖ group (32) ‖ commit (32) ‖ nlinks (u32, big-endian) ‖ links (32 each) ‖ author (16)

Every field has a fixed size except the links, and each link has a fixed size. So the length of
the bytes alone fixes the number of links, and different records always have different
encodings (`decode_encode` below; `encode_injective` follows from it).

`decode` is strict: it accepts exactly the outputs of `encode` (`encode_of_decode`). It rejects a
wrong tag, a wrong length, an `nlinks` field that does not match the length, and links that are
not strictly increasing (`StrictlySorted`).

**Record digest:** `hashRecord r := sha256 (encode r)`. It is defined here rather than in
`Zrdt.Record` because it needs `encode`.

**Store blob:**

    "zrdtS2" ‖ group (32) ‖ count (u32) ‖ (len (u32) ‖ record)*

The store writes its records sorted by digest. `decodeBlob` checks the framing strictly (every
length exact, no bytes left over, every record strictly decoded; `encodeBlob_of_decodeBlob`). It
does not check the order of the records or the group inside each record: the store's `open`
checks the group when it accepts them, and the order does not change the store. A well-sized
blob decodes back to what was written (`decodeBlob_encodeBlob`).

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


/-! ## What the encoders guarantee

The main statements:

- `decode_encode`: decoding an encoded record gives it back, for every record (no size bound).
  So `encode` never maps two records to the same bytes.
- `encode_of_decode`: `decode` is strict. Whatever it accepts is exactly the encoding of the
  record it returns, so each record has one encoding and nothing else decodes.
- `decodeBlob_encodeBlob`: a well-sized list of records written as a blob decodes back to the
  same group and records, in the same order.
- `encodeBlob_of_decodeBlob`: whatever `decodeBlob` accepts is exactly the blob `encodeBlob`
  writes for the group and records it returns.

The helper lemmas come first. -/

namespace Encode

/-! ### Byte arrays -/

/-- The middle part of `p ++ (m ++ s)`. -/
theorem extract_append_mid {p m s : ByteArray} {i j : Nat} (hi : i = p.size)
    (hj : j = p.size + m.size) : (p ++ (m ++ s)).extract i j = m := by
  subst hi hj
  rw [ByteArray.extract_append, Nat.sub_self, Nat.add_sub_cancel_left,
    ByteArray.extract_append_eq_left rfl, ByteArray.extract_eq_empty_iff.mpr (by omega),
    ByteArray.empty_append]

/-- Two neighbouring slices join into one. -/
theorem extract_join {b : ByteArray} {i j k : Nat} (hij : i ≤ j) (hjk : j ≤ k) :
    b.extract i j ++ b.extract j k = b.extract i k :=
  (ByteArray.extract_eq_extract_append_extract j hij hjk).symm

/-- A passing `guard` means its condition holds. -/
theorem guard_eq_some {p : Prop} [Decidable p] {u : Unit}
    (h : (if p then some () else failure : Option Unit) = some u) : p := by
  split at h
  · assumption
  · cases h

/-! ### Fixed parts -/

@[simp] theorem size_u32be (n : Nat) : (u32be n).size = 4 := rfl
@[simp] theorem size_recordTag : recordTag.size = 5 := by decide
@[simp] theorem size_blobTag : blobTag.size = 6 := by decide

/-- A byte equals `n.toUInt8` when it is `n` mod 256. -/
theorem toUInt8_eq_of_mod {n : Nat} {x : UInt8} (h : n % 256 = x.toNat) : n.toUInt8 = x := by
  apply UInt8.toNat_inj.mp
  simpa using h

/-- `u32be` writes only the low 32 bits. -/
theorem u32be_mod (n : Nat) : u32be (n % 2^32) = u32be n := by
  simp only [u32be, Nat.shiftRight_eq_div_pow, ByteArray.mk.injEq, Array.mk.injEq,
    List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> apply toUInt8_eq_of_mod <;> simp <;> omega

/-- Reading back 4 bytes written by `u32be n` gives `n % 2^32`. -/
theorem readU32?_of_extract {b : ByteArray} {off n : Nat}
    (h : b.extract off (off + 4) = u32be n) : readU32? b off = some (n % 2^32) := by
  have hs : off + 4 ≤ b.size := by
    have := congrArg ByteArray.size h
    simp [ByteArray.size_extract] at this
    omega
  have hb : ∀ k (hk : k < 4), b[off + k]'(by omega) = (u32be n)[k]'(by simpa using hk) := by
    intro k hk
    rw [← ByteArray.getElem_extract (start := off) (stop := off + 4)
      (by simp [ByteArray.size_extract]; omega)]
    simp only [h]
  unfold readU32?
  rw [dite_eq_left hs]
  have h0 := hb 0 (by omega)
  have h1 := hb 1 (by omega)
  have h2 := hb 2 (by omega)
  have h3 := hb 3 (by omega)
  simp only [Nat.add_zero] at h0
  rw [h0, h1, h2, h3]
  simp [u32be, ByteArray.getElem_eq_getElem_data, Nat.shiftRight_eq_div_pow]
  omega

/-- The 4 bytes `readU32?` read are `u32be` of the number it returned. -/
theorem extract_of_readU32? {b : ByteArray} {off m : Nat} (h : readU32? b off = some m) :
    b.extract off (off + 4) = u32be m := by
  unfold readU32? at h
  split at h
  · rename_i hs
    cases h
    rw [ByteArray.extract_add_four hs]
    apply ByteArray.ext
    simp only [List.data_toByteArray, u32be, Nat.shiftRight_eq_div_pow, Array.mk.injEq,
      List.cons.injEq, and_true]
    have := b[off].toNat_lt
    have := b[off+1].toNat_lt
    have := b[off+2].toNat_lt
    have := b[off+3].toNat_lt
    refine ⟨?_, ?_, ?_, ?_⟩ <;> (apply Eq.symm; apply toUInt8_eq_of_mod) <;> simp <;> omega
  · cases h

/-! ### Links -/

/-- The links of a list, written one after another (the list form of `linksBytes`). -/
def linksBytesList : List Digest → ByteArray
  | [] => ByteArray.empty
  | d :: ds => d.bytes ++ linksBytesList ds

open Examples in
#guard linksBytesList [dig 1, dig 2] == linksBytes #[dig 1, dig 2]

theorem foldl_append_bytes (l : List Digest) (init : ByteArray) :
    l.foldl (fun acc d => acc ++ d.bytes) init = init ++ linksBytesList l := by
  induction l generalizing init with
  | nil => simp [linksBytesList, ByteArray.append_empty]
  | cons d ds ih => simp [linksBytesList, ih, ByteArray.append_assoc]

theorem linksBytes_eq (ls : Array Digest) : linksBytes ls = linksBytesList ls.toList := by
  rw [linksBytes, ← Array.foldl_toList, foldl_append_bytes, ByteArray.empty_append]

theorem size_linksBytesList (l : List Digest) : (linksBytesList l).size = 32 * l.length := by
  induction l with
  | nil => rfl
  | cons d ds ih => simp [linksBytesList, ByteArray.size_append, ih, d.size_eq]; omega

@[simp] theorem size_linksBytes (ls : Array Digest) : (linksBytes ls).size = 32 * ls.size := by
  simp [linksBytes_eq, size_linksBytesList]

theorem linksBytes_append (xs ys : Array Digest) :
    linksBytes (xs ++ ys) = linksBytes xs ++ linksBytes ys := by
  simp only [linksBytes_eq, Array.toList_append]
  induction xs.toList with
  | nil => simp [linksBytesList, ByteArray.empty_append]
  | cons d ds ih => simp [linksBytesList, ih, ByteArray.append_assoc]

/-- `readDigests` reads back links written by `linksBytes`. -/
theorem readDigests_linksBytesList (l : List Digest) (p s : ByteArray) (acc : Array Digest) :
    readDigests (p ++ (linksBytesList l ++ s)) p.size acc l.length =
      some (acc ++ l.toArray) := by
  induction l generalizing p acc with
  | nil => simp [readDigests]
  | cons d ds ih =>
    have hx : (p ++ (linksBytesList (d :: ds) ++ s)).extract p.size (p.size + 32) = d.bytes := by
      simp only [linksBytesList, ByteArray.append_assoc]
      exact extract_append_mid rfl (by rw [d.size_eq])
    have hr : p ++ (linksBytesList (d :: ds) ++ s) =
        (p ++ d.bytes) ++ (linksBytesList ds ++ s) := by
      simp [linksBytesList, ByteArray.append_assoc]
    have hsz : (p ++ d.bytes).size = p.size + 32 := by simp [ByteArray.size_append, d.size_eq]
    simp only [List.length_cons, readDigests, hx, Digest.ofBytes?_bytes, Option.bind_eq_bind,
      Option.bind_some]
    rw [hr, ← hsz, ih]
    simp

/-- What `readDigests` returns is `acc` plus digests whose bytes are exactly the bytes it read. -/
theorem readDigests_spec {b : ByteArray} {off k : Nat} {acc res : Array Digest}
    (h : readDigests b off acc k = some res) :
    ∃ ls : Array Digest, res = acc ++ ls ∧ ls.size = k ∧
      linksBytes ls = b.extract off (off + 32 * k) := by
  induction k generalizing off acc with
  | zero =>
    simp only [readDigests, Option.some.injEq] at h
    exact ⟨#[], by simp [h], rfl, by simp [linksBytes, ByteArray.extract_same]⟩
  | succ k ih =>
    simp only [readDigests, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨d, hd, hrest⟩ := h
    obtain ⟨ls, hres, hsize, hbytes⟩ := ih hrest
    refine ⟨#[d] ++ ls, by simp [hres], by simp [hsize]; omega, ?_⟩
    rw [linksBytes_append, hbytes]
    have : linksBytes #[d] = b.extract off (off + 32) := by
      rw [← Digest.bytes_of_ofBytes? hd]; simp [linksBytes, ByteArray.empty_append]
    rw [this, ByteArray.extract_append_extract, Nat.min_eq_left (by omega),
      Nat.max_eq_right (by omega)]
    congr 1; omega

end Encode

open Encode

/-! ### Records -/

/-- A record with `n` links takes `89 + 32 n` bytes. -/
theorem size_encode (r : Rec) : (encode r).size = encodedSize r.links.size := by
  simp [encode, encodedSize, ByteArray.size_append, r.group.size_eq, r.commit.size_eq,
    r.author.size_eq]
  omega

/-- Decoding an encoded record gives it back. This holds for every record, with no size bound,
so two different records never have the same encoding. -/
theorem decode_encode (r : Rec) : decode (encode r) = some r := by
  obtain ⟨g, c, ls, a, hls⟩ := r
  -- the encoding, split around each field
  have e1 : encode ⟨g, c, ls, a, hls⟩ = recordTag ++ (g.bytes ++ (c.bytes ++ (u32be ls.size ++
      (linksBytes ls ++ a.bytes)))) := by simp [encode, ByteArray.append_assoc]
  have e2 : encode ⟨g, c, ls, a, hls⟩ = (recordTag ++ g.bytes) ++ (c.bytes ++ (u32be ls.size ++
      (linksBytes ls ++ a.bytes))) := by simp [encode, ByteArray.append_assoc]
  have e3 : encode ⟨g, c, ls, a, hls⟩ = (recordTag ++ g.bytes ++ c.bytes) ++ (u32be ls.size ++
      (linksBytes ls ++ a.bytes)) := by simp [encode, ByteArray.append_assoc]
  have e4 : encode ⟨g, c, ls, a, hls⟩ = (recordTag ++ g.bytes ++ c.bytes ++ u32be ls.size) ++
      (linksBytesList ls.toList ++ a.bytes) := by
    simp [encode, ByteArray.append_assoc, linksBytes_eq]
  have e5 : encode ⟨g, c, ls, a, hls⟩ = (recordTag ++ g.bytes ++ c.bytes ++ u32be ls.size ++
      linksBytes ls) ++ a.bytes := rfl
  have hsize := size_encode ⟨g, c, ls, a, hls⟩
  simp only [encodedSize] at hsize
  have hn : ((encode ⟨g, c, ls, a, hls⟩).size - 89) / 32 = ls.size := by omega
  have htag : (encode ⟨g, c, ls, a, hls⟩).extract 0 5 = recordTag := by
    rw [e1]; exact ByteArray.extract_append_eq_left (by simp)
  have hg : (encode ⟨g, c, ls, a, hls⟩).extract 5 37 = g.bytes := by
    rw [e1]; exact extract_append_mid (by simp) (by simp [g.size_eq])
  have hc : (encode ⟨g, c, ls, a, hls⟩).extract 37 69 = c.bytes := by
    rw [e2]; exact extract_append_mid (by simp [ByteArray.size_append, g.size_eq])
      (by simp [ByteArray.size_append, g.size_eq, c.size_eq])
  have hu : readU32? (encode ⟨g, c, ls, a, hls⟩) 69 = some (ls.size % 2^32) := by
    apply readU32?_of_extract
    rw [e3]; exact extract_append_mid (by simp [ByteArray.size_append, g.size_eq, c.size_eq])
      (by simp [ByteArray.size_append, g.size_eq, c.size_eq])
  have hl : readDigests (encode ⟨g, c, ls, a, hls⟩) 73 #[] ls.size = some ls := by
    have := readDigests_linksBytesList ls.toList
      (recordTag ++ g.bytes ++ c.bytes ++ u32be ls.size) a.bytes #[]
    simp only [ByteArray.size_append, size_recordTag, g.size_eq, c.size_eq, size_u32be,
      Array.length_toList, Array.toArray_toList, Array.empty_append] at this
    rw [e4]; exact this
  have ha : (encode ⟨g, c, ls, a, hls⟩).extract (73 + 32 * ls.size)
      (encode ⟨g, c, ls, a, hls⟩).size = a.bytes := by
    rw [e5]; exact ByteArray.extract_append_eq_right
      (by simp [ByteArray.size_append, g.size_eq, c.size_eq]) (by simp [ByteArray.size_append])
  simp only [decode, hn, htag, hu, hg, hc, hl, ha, GroupId.ofBytes?_bytes, Digest.ofBytes?_bytes,
    Aci.ofBytes?_bytes]
  simp [guard, hsize, hls]

/-- `decode` is strict: whatever it accepts is exactly the encoding of the record it returns. -/
theorem encode_of_decode {b : ByteArray} {r : Rec} (h : decode b = some r) : encode r = b := by
  simp only [decode, guard, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff] at h
  obtain ⟨_, h1, _, h2, _, h3, g, hg, c, hc, ls, hls, a, ha, hr⟩ := h
  have h1 := guard_eq_some h1
  have h2 := guard_eq_some h2
  have h3 := guard_eq_some h3
  split at hr
  · cases hr
    obtain ⟨ls', rfl, hsize, hbytes⟩ := readDigests_spec hls
    simp only [encode, Array.empty_append]
    -- name the link count
    generalize hn : (b.size - 89) / 32 = n at *
    have hb : b.size = 73 + 32 * n + 16 := by omega
    rw [hsize, ← u32be_mod, ← extract_of_readU32? h3, hbytes, GroupId.bytes_of_ofBytes? hg,
      Digest.bytes_of_ofBytes? hc, Aci.bytes_of_ofBytes? ha, ← h2]
    simp only [Nat.reduceAdd]
    rw [extract_join (by omega) (by omega), extract_join (by omega) (by omega),
      extract_join (by omega) (by omega), extract_join (by omega) (by omega),
      extract_join (by omega) (by omega), ByteArray.extract_zero_size]
  · cases hr

/-- `decode b` returns `r` exactly when `b` is the encoding of `r`. -/
theorem decode_eq_some_iff {b : ByteArray} {r : Rec} : decode b = some r ↔ encode r = b :=
  ⟨encode_of_decode, fun h => h ▸ decode_encode r⟩

example : decode (encode Examples.reply) = some Examples.reply := decode_encode _
example : ¬ decode ((encode Examples.first).push 0) = some Examples.first := by
  rw [decode_eq_some_iff]
  intro h
  have := congrArg ByteArray.size h
  simp [ByteArray.size_push] at this

/-! ### Blobs -/

namespace Encode

/-- The entries `len ‖ record` of a list of records, one after another. -/
def entriesBytes : List Rec → ByteArray
  | [] => ByteArray.empty
  | r :: rs => (u32be (encode r).size ++ encode r) ++ entriesBytes rs

open Examples in
#guard (entriesBytes [first]).size == 4 + 89

theorem foldl_entries (l : List Rec) (init : ByteArray) :
    l.foldl (fun acc r => let e := encode r; acc ++ u32be e.size ++ e) init =
      init ++ entriesBytes l := by
  induction l generalizing init with
  | nil => simp [entriesBytes, ByteArray.append_empty]
  | cons r rs ih =>
    rw [List.foldl_cons, ih]
    simp [entriesBytes, ByteArray.append_assoc]

theorem encodeBlob_eq (g : GroupId) (rs : Array Rec) :
    encodeBlob g rs = blobTag ++ g.bytes ++ u32be rs.size ++ entriesBytes rs.toList := by
  rw [encodeBlob, ← Array.foldl_toList, foldl_entries]

/-- Every entry takes at least `minEntrySize` bytes. -/
theorem size_entriesBytes_ge (l : List Rec) :
    minEntrySize * l.length ≤ (entriesBytes l).size := by
  induction l with
  | nil => simp [entriesBytes]
  | cons r rs ih =>
    simp only [entriesBytes, ByteArray.size_append, size_u32be, size_encode, encodedSize,
      minEntrySize, List.length_cons] at ih ⊢
    rw [Nat.mul_add]; omega

/-- `readRecords` reads back entries written by `entriesBytes`, when every record's encoding
fits its 32-bit length field. -/
theorem readRecords_entriesBytes (l : List Rec) (hl : ∀ r ∈ l, (encode r).size < 2^32)
    (p s : ByteArray) (acc : Array Rec) :
    readRecords (p ++ (entriesBytes l ++ s)) p.size acc l.length =
      some (acc ++ l.toArray, p.size + (entriesBytes l).size) := by
  induction l generalizing p acc with
  | nil => simp [readRecords, entriesBytes]
  | cons r rs ih =>
    have hlt : (encode r).size < 2^32 := hl r List.mem_cons_self
    have hrest : ∀ r ∈ rs, (encode r).size < 2^32 := fun r h => hl r (List.mem_cons_of_mem _ h)
    have hu : readU32? (p ++ (entriesBytes (r :: rs) ++ s)) p.size = some (encode r).size := by
      rw [readU32?_of_extract (n := (encode r).size), Nat.mod_eq_of_lt hlt]
      simp only [entriesBytes, ByteArray.append_assoc]
      exact extract_append_mid rfl (by simp)
    have hsz : (p ++ (entriesBytes (r :: rs) ++ s)).size =
        p.size + 4 + (encode r).size + (entriesBytes rs).size + s.size := by
      simp [entriesBytes, ByteArray.size_append]; omega
    have hx : (p ++ (entriesBytes (r :: rs) ++ s)).extract (p.size + 4)
        (p.size + 4 + (encode r).size) = encode r := by
      have : p ++ (entriesBytes (r :: rs) ++ s) =
          (p ++ u32be (encode r).size) ++ (encode r ++ (entriesBytes rs ++ s)) := by
        simp [entriesBytes, ByteArray.append_assoc]
      rw [this]; exact extract_append_mid (by simp [ByteArray.size_append])
        (by simp [ByteArray.size_append])
    have hr : p ++ (entriesBytes (r :: rs) ++ s) =
        (p ++ u32be (encode r).size ++ encode r) ++ (entriesBytes rs ++ s) := by
      simp [entriesBytes, ByteArray.append_assoc]
    have hpsz : (p ++ u32be (encode r).size ++ encode r).size = p.size + 4 + (encode r).size := by
      simp [ByteArray.size_append]
    simp only [List.length_cons, readRecords, hu, hx, decode_encode, Option.bind_eq_bind,
      Option.bind_some, hsz]
    have hg : p.size + 4 + (encode r).size ≤
        p.size + 4 + (encode r).size + (entriesBytes rs).size + s.size := by omega
    simp only [guard, hg, ↓reduceIte, Option.pure_def, Option.bind_some]
    rw [hr, ← hpsz, ih hrest]
    simp [entriesBytes, ByteArray.size_append]
    omega

/-- What `readRecords` returns is `acc` plus records whose entries are exactly the bytes it read. -/
theorem readRecords_spec {b : ByteArray} {off k stop : Nat} {acc res : Array Rec}
    (h : readRecords b off acc k = some (res, stop)) :
    ∃ l : List Rec, res = acc ++ l.toArray ∧ l.length = k ∧ off ≤ stop ∧
      entriesBytes l = b.extract off stop := by
  induction k generalizing off acc with
  | zero =>
    simp only [readRecords, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨[], by simp, rfl, Nat.le_refl _, by simp [entriesBytes, ByteArray.extract_same]⟩
  | succ k ih =>
    simp only [readRecords, guard, Option.bind_eq_bind, Option.pure_def,
      Option.bind_eq_some_iff] at h
    obtain ⟨len, hlen, _, hg, r, hr, hrest⟩ := h
    have hg := guard_eq_some hg
    obtain ⟨l, hres, hl, hle, hbytes⟩ := ih hrest
    have henc := encode_of_decode hr
    have hsize : (encode r).size = len := by
      rw [henc, ByteArray.size_extract]; omega
    refine ⟨r :: l, by simp [hres], by simp [hl], by omega, ?_⟩
    simp only [entriesBytes]
    rw [hbytes, hsize, henc, ← extract_of_readU32? hlen, extract_join (by omega) (by omega),
      extract_join (by omega) hle]

end Encode

/-- A well-sized list of records, written as a blob, decodes back to the same group and records
in the same order. -/
theorem decodeBlob_encodeBlob (g : GroupId) (rs : Array Rec) (h : WellSized rs) :
    decodeBlob (encodeBlob g rs) = some (g, rs) := by
  have hrec : ∀ r ∈ rs.toList, (encode r).size < 2^32 := by
    intro r hr
    have := h.2 r (Array.mem_toList_iff.mp hr)
    simp only [Rec.WellSized, maxLinks] at this
    rw [size_encode, encodedSize]; omega
  have hcount : rs.size < 2^32 := by
    have := h.1; simp only [maxRecords] at this; omega
  rw [encodeBlob_eq]
  have e1 : blobTag ++ g.bytes ++ u32be rs.size ++ entriesBytes rs.toList =
      blobTag ++ (g.bytes ++ (u32be rs.size ++ entriesBytes rs.toList)) := by
    simp [ByteArray.append_assoc]
  have e2 : blobTag ++ g.bytes ++ u32be rs.size ++ entriesBytes rs.toList =
      (blobTag ++ g.bytes) ++ (u32be rs.size ++ entriesBytes rs.toList) := by
    simp [ByteArray.append_assoc]
  have e3 : blobTag ++ g.bytes ++ u32be rs.size ++ entriesBytes rs.toList =
      (blobTag ++ g.bytes ++ u32be rs.size) ++ (entriesBytes rs.toList ++ ByteArray.empty) := by
    simp [ByteArray.append_empty]
  have hsize : (blobTag ++ g.bytes ++ u32be rs.size ++ entriesBytes rs.toList).size =
      42 + (entriesBytes rs.toList).size := by
    simp [ByteArray.size_append, g.size_eq]
  have htag : (blobTag ++ g.bytes ++ u32be rs.size ++ entriesBytes rs.toList).extract 0 6 =
      blobTag := by
    rw [e1]; exact ByteArray.extract_append_eq_left (by simp)
  have hg : (blobTag ++ g.bytes ++ u32be rs.size ++ entriesBytes rs.toList).extract 6 38 =
      g.bytes := by
    rw [e1]; exact extract_append_mid (by simp) (by simp [g.size_eq])
  have hu : readU32? (blobTag ++ g.bytes ++ u32be rs.size ++ entriesBytes rs.toList) 38 =
      some rs.size := by
    rw [readU32?_of_extract (n := rs.size), Nat.mod_eq_of_lt hcount]
    rw [e2]; exact extract_append_mid (by simp [ByteArray.size_append, g.size_eq])
      (by simp [ByteArray.size_append, g.size_eq])
  have hmin : rs.size * minEntrySize ≤ (entriesBytes rs.toList).size := by
    have := size_entriesBytes_ge rs.toList
    rw [Array.length_toList] at this
    rw [Nat.mul_comm]; exact this
  have hread : readRecords (blobTag ++ g.bytes ++ u32be rs.size ++ entriesBytes rs.toList) 42 #[]
      rs.size = some (rs, 42 + (entriesBytes rs.toList).size) := by
    have := readRecords_entriesBytes rs.toList hrec (blobTag ++ g.bytes ++ u32be rs.size)
      ByteArray.empty #[]
    simp only [ByteArray.size_append, size_blobTag, g.size_eq, size_u32be, Array.length_toList,
      Array.toArray_toList, Array.empty_append] at this
    rw [e3]; exact this
  simp only [decodeBlob, hsize, htag, hg, hu, GroupId.ofBytes?_bytes]
  simp [guard, hmin]
  rw [hread]
  simp

/-- `decodeBlob` is strict about framing: whatever it accepts is exactly the blob `encodeBlob`
writes for the group and records it returns. -/
theorem encodeBlob_of_decodeBlob {b : ByteArray} {g : GroupId} {rs : Array Rec}
    (h : decodeBlob b = some (g, rs)) : encodeBlob g rs = b := by
  simp only [decodeBlob, guard, Option.bind_eq_bind, Option.pure_def,
    Option.bind_eq_some_iff] at h
  obtain ⟨_, h1, _, h2, g', hg, count, hcount, _, h3, ⟨rs', stop⟩, hread, _, h4, hout⟩ := h
  have h1 := guard_eq_some h1
  have h2 := guard_eq_some h2
  have h4 := guard_eq_some h4
  simp only [Option.some.injEq, Prod.mk.injEq] at hout
  obtain ⟨rfl, rfl⟩ := hout
  obtain ⟨l, hres, hl, hle, hbytes⟩ := readRecords_spec hread
  simp only at h4
  subst h4
  rw [hres, Array.empty_append, encodeBlob_eq, List.size_toArray, hl, List.toList_toArray,
    hbytes, ← extract_of_readU32? hcount, GroupId.bytes_of_ofBytes? hg, ← h2]
  simp only [Nat.reduceAdd]
  rw [extract_join (by omega) (by omega), extract_join (by omega) (by omega),
    extract_join (by omega) (by omega), ByteArray.extract_zero_size]

example : decodeBlob (encodeBlob Examples.group #[Examples.first, Examples.reply]) =
    some (Examples.group, #[Examples.first, Examples.reply]) :=
  decodeBlob_encodeBlob _ _ (by decide +kernel)

end Zrdt
