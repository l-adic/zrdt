import Zrdt.Digest

/-!
# SHA-256 in pure Lean

SHA-256 as specified in FIPS 180-4, written plainly and not optimised. It has no `@[extern]`, no
`opaque` and no C, so it runs under `#eval` and inside the kernel, and the build checks it
against the NIST example vectors below.

Adapted from the review prototype (`pure-lean-core/Sha256.lean`). Changes: the eight working
words are a structure instead of an array, and the result is a `Digest` whose size is 32 by
construction, so there is no fallback branch.
-/

namespace Zrdt.Sha256

/-- The 64 round constants (FIPS 180-4 §4.2.2). -/
def K : Array UInt32 := #[
  0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
  0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
  0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
  0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
  0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
  0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
  0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
  0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2]

example : K.size = 64 := rfl

/-- The eight 32-bit working words `a` to `h`. -/
structure State where
  a : UInt32
  b : UInt32
  c : UInt32
  d : UInt32
  e : UInt32
  f : UInt32
  g : UInt32
  h : UInt32

/-- The initial hash value (FIPS 180-4 §5.3.3). -/
def H0 : State :=
  ⟨0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19⟩

/-- Rotate a word right by `n` bits (`0 < n < 32`). -/
@[inline] def rotr (x n : UInt32) : UInt32 := (x >>> n) ||| (x <<< (32 - n))

example : rotr 1 1 = 0x80000000 := rfl

/-- Padding: append the byte `0x80`, then zero bytes until the length is 56 mod 64, then the
message length in bits as a big-endian 64-bit number. The result is a whole number of 64-byte
blocks. -/
def pad (msg : ByteArray) : ByteArray := Id.run do
  let zeros := (64 + 56 - (msg.size + 1) % 64) % 64
  let mut b := msg.push 0x80
  for _ in [0:zeros] do
    b := b.push 0
  let bits : UInt64 := msg.size.toUInt64 * 8
  for i in [0:8] do
    b := b.push (bits >>> (56 - 8 * i).toUInt64).toUInt8
  return b

#guard (pad ByteArray.empty).size == 64
#guard (pad ⟨Array.replicate 55 0⟩).size == 64
#guard (pad ⟨Array.replicate 56 0⟩).size == 128

/-- The big-endian 32-bit word at byte offset `i`. -/
@[inline] def word (p : ByteArray) (i : Nat) : UInt32 :=
  (p[i]!.toUInt32 <<< 24) ||| (p[i+1]!.toUInt32 <<< 16) ||| (p[i+2]!.toUInt32 <<< 8) |||
    p[i+3]!.toUInt32

example : word ⟨#[1, 2, 3, 4]⟩ 0 = 0x01020304 := by decide

/-- The 64-word message schedule of the 64-byte block at offset `off` (FIPS 180-4 §6.2.2). -/
def schedule (p : ByteArray) (off : Nat) : Array UInt32 := Id.run do
  let mut w : Array UInt32 := Array.emptyWithCapacity 64
  for i in [0:16] do
    w := w.push (word p (off + 4 * i))
  for i in [16:64] do
    let s0 := rotr w[i-15]! 7 ^^^ rotr w[i-15]! 18 ^^^ (w[i-15]! >>> 3)
    let s1 := rotr w[i-2]! 17 ^^^ rotr w[i-2]! 19 ^^^ (w[i-2]! >>> 10)
    w := w.push (w[i-16]! + s0 + w[i-7]! + s1)
  return w

#guard (schedule (pad ByteArray.empty) 0).size == 64

/-- One round of the compression function, with round constant `k` and schedule word `w`. -/
@[inline] def round (s : State) (k w : UInt32) : State :=
  let S1 := rotr s.e 6 ^^^ rotr s.e 11 ^^^ rotr s.e 25
  let ch := (s.e &&& s.f) ^^^ ((~~~s.e) &&& s.g)
  let t1 := s.h + S1 + ch + k + w
  let S0 := rotr s.a 2 ^^^ rotr s.a 13 ^^^ rotr s.a 22
  let maj := (s.a &&& s.b) ^^^ (s.a &&& s.c) ^^^ (s.b &&& s.c)
  ⟨t1 + S0 + maj, s.a, s.b, s.c, s.d + t1, s.e, s.f, s.g⟩

/-- Process the 64-byte block at offset `off`: 64 rounds, then add the result to the input
state word by word. -/
def compress (h : State) (p : ByteArray) (off : Nat) : State := Id.run do
  let w := schedule p off
  let mut s := h
  for i in [0:64] do
    s := round s K[i]! w[i]!
  return ⟨h.a + s.a, h.b + s.b, h.c + s.c, h.d + s.d, h.e + s.e, h.f + s.f, h.g + s.g, h.h + s.h⟩

/-- The 32 output bytes: each word big-endian, `a` first. -/
def State.toBytes (s : State) : ByteArray :=
  let be (x : UInt32) : List UInt8 :=
    [(x >>> 24).toUInt8, (x >>> 16).toUInt8, (x >>> 8).toUInt8, x.toUInt8]
  ⟨(be s.a ++ be s.b ++ be s.c ++ be s.d ++ be s.e ++ be s.f ++ be s.g ++ be s.h).toArray⟩

/-- The output always has 32 bytes. -/
theorem State.size_toBytes (s : State) : s.toBytes.size = 32 := rfl

end Sha256

/-- SHA-256 of a byte string (FIPS 180-4). -/
def sha256 (msg : ByteArray) : Digest := Id.run do
  let p := Sha256.pad msg
  let mut h := Sha256.H0
  for k in [0:p.size / 64] do
    h := Sha256.compress h p (64 * k)
  return ⟨h.toBytes, h.size_toBytes⟩

/-! ## NIST example vectors (FIPS 180-4 examples, checked at build time) -/

-- The empty message.
#guard (sha256 ByteArray.empty).toHex ==
  "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
-- "abc", one block.
#guard (sha256 "abc".toUTF8).toHex ==
  "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
-- The 448-bit message: 56 bytes, so the padding needs a second block.
#guard (sha256 "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq".toUTF8).toHex ==
  "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1"
-- The 896-bit message: 112 bytes, two blocks.
#guard (sha256 ("abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghijklmnhijklmno" ++
    "ijklmnopjklmnopqklmnopqrlmnopqrsmnopqrstnopqrstu").toUTF8).toHex ==
  "cf5b16a778af8380036ce59e7b0492370b249b11e8f07a51afac45037afee9d1"
-- One million bytes of `a` (15,626 blocks).
#guard (sha256 ⟨Array.replicate 1000000 97⟩).toHex ==
  "cdc76e5c9914fb9281a1c7e284d73e67f1809a48a497200e046d39ccc7112cd0"

/-! ## Padding boundaries (expected values from Python's `hashlib`)

The message is bytes `(7 i + 3) mod 256` for `i < n`. The lengths sit on both sides of the
56-byte and 64-byte padding boundaries. -/

/-- The test message of length `n`. -/
def boundaryMsg (n : Nat) : ByteArray := ⟨(Array.range n).map fun i => (7 * i + 3).toUInt8⟩

#guard [1, 55, 56, 63, 64, 65, 119, 120, 127, 128, 129, 1000].map
    (fun n => (sha256 (boundaryMsg n)).toHex) == [
  "084fed08b978af4d7d196a7446a86b58009e636b611db16211b65a9aadff29c5",
  "e7313d333c272e639f790978283f9eb392e843d0f29b7016828bb1daa4aac70b",
  "4324d65f3c103567f5589c710bc08f8523f929a9272e3af36fc968e52abc6c27",
  "81c80242132f230c3bd41b3e63bbcff16107339549214a99614ff26664625055",
  "39e3d7b6b5d075d37d053ad89b24b41bef4f3c29760c84447cab3f3be1882241",
  "aacca6ff74fdbb296d165a45cecfa04e5127bc008770fbbdd48006f2d2fae95e",
  "9ce7368e4daf32341631b492e80359dc9f594b48453cd0dd5bf0b19279cc177e",
  "7836b787757e95e58b3ca5aec90b1b004e8deba1e50e9675af9cabf1a13a04b5",
  "a8d23e75d936f303d248888d9b165ee543f4cbafcad3c9dd2a79bd84faa11d07",
  "d2742f1f4ac6bb7ca2b239ee18402ba8b3f9f8e652d2a72973c2b9ba11c08cf6",
  "307f8fc2c1622b92762e818d39a185d4d667ad49a4b07ceae1f4afa008a93ec4",
  "1e9bc38cbf860b9ec31918b065f9b52476c549a782e0e7990bed8ce3868d2371"]

/-! ## The kernel can run it

`decide +kernel` makes the kernel itself evaluate `sha256` (no compiled code involved). One block
takes a few seconds, so only "abc" is checked this way. -/

example : sha256 "abc".toUTF8 = (Digest.ofHex?
    "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad").get! := by
  decide +kernel

end Zrdt
