-- Reference copy from the JOIN_PLAN v2 review (2026-11-01). Not built by any lake target. No sorry.
-- NOT ADOPTED (review round 1, JOIN_PLAN §10a): a tag list broadcast to the group is not deniable;
-- every holder keeps tag_X, which only the author or X can compute (a two-witness proof), and
-- `reader_can_forge` below does not account for an independent holder. Kept only for HMAC and
-- HKDF over the shipped SHA-256 (RFC 4231 / RFC 5869 vectors). `pairKey` also differs from the
-- construction v2 had written in §10a.
import Zrdt.Commit

/-!
# Scratch: addressee slots (designated-verifier tags) for zrdt3 — JOIN design check

Not part of the build. Checks, against the shipped pure-Lean SHA-256:
1. HMAC-SHA256 / HKDF-SHA256 over `Zrdt.sha256` match RFC 4231 / RFC 5869 vectors
   (so tags can be computed in zrdtd and "the host never hashes" survives);
2. the responder function never releases an opening except to the author or to a requester
   whose slot is in the record, and only an opening that matches the record (`respond_scoped`);
3. the newcomer's leaf check refuses every leaf that carries his slot (`leafVerdict_notForYou`),
   so an honestly built record addressed to him can never be accepted as a leaf
   (`addressed_never_leaf`);
4. MAC deniability in witness form: the designated reader can build, from the pairwise key
   alone, a record "by A" that passes his own check (`reader_can_forge`).
-/

namespace Zrdt.Dvs
open Zrdt

/-! ## HMAC-SHA256 and HKDF-SHA256 over the shipped SHA-256 -/

def padKey (k : ByteArray) (p : UInt8) : ByteArray :=
  ⟨(Array.range 64).map fun i => (if h : i < k.size then k[i] else 0) ^^^ p⟩

def hmac (key msg : ByteArray) : Digest :=
  let k := if key.size > 64 then (sha256 key).bytes else key
  sha256 (padKey k 0x5c ++ (sha256 (padKey k 0x36 ++ msg)).bytes)

/-- HKDF-SHA256 with a 32-byte output (one block). -/
def hkdf32 (salt ikm info : ByteArray) : Digest :=
  let prk := hmac salt ikm
  hmac prk.bytes (info ++ ⟨#[1]⟩)

def hex (xs : List Nat) : ByteArray := ⟨xs.toArray.map (·.toUInt8)⟩

-- RFC 4231 test case 1 and 2.
#guard (hmac ⟨Array.replicate 20 0x0b⟩ "Hi There".toUTF8).toHex ==
  "b0344c61d8db38535ca8afceaf0bf12b881dc200c9833da726e9376c2e32cff7"
#guard (hmac "Jefe".toUTF8 "what do ya want for nothing?".toUTF8).toHex ==
  "5bdcc146bf60754e6a042426089575c75a003f089d2739839dec58b964ec3843"
-- RFC 4231 test case 6: 131-byte key (hashed first).
#guard (hmac ⟨Array.replicate 131 0xaa⟩
    "Test Using Larger Than Block-Size Key - Hash Key First".toUTF8).toHex ==
  "60e431591ee0b67f0d8a26aacbf5b77f8e0bc6213728c5140546040f0ee37f54"
-- RFC 5869 test case 1 (first 32 bytes of OKM).
#guard (hkdf32 (hex (List.range 13)) ⟨Array.replicate 22 0x0b⟩
    (hex ((List.range 10).map (· + 0xf0)))).toHex ==
  "3cb25f25faacd57a90434f64d0362f2a2d2d0a90cf1a5a4c5db02d56ecc4c5bf"

/-! ## Slots, leaves, full records -/

structure Slot where
  bytes : ByteArray
  size_eq : bytes.size = 16
deriving DecidableEq

def dvLabel : ByteArray := "zrdt-dv1".toUTF8

/-- The pairwise key of `a` and `x` for group `g`, from the X25519 output (computed by the host
with libsignal `PrivateKey.agree`; symmetric in `a`, `x`). -/
def pairKey (shared : ByteArray) (g : GroupId) : ByteArray := (hkdf32 dvLabel shared g.bytes).bytes

def linksBytes' (ls : Array Digest) : ByteArray := ls.foldl (fun acc d => acc ++ d.bytes) .empty

/-- Tag from author `a` to reader `x` over the record's core and links. -/
def tag (k : ByteArray) (g : GroupId) (a x : Aci) (core : Digest) (links : Array Digest) : Digest :=
  hmac k (dvLabel ++ g.bytes ++ a.bytes ++ x.bytes ++ core.bytes ++ u32be links.size ++
    linksBytes' links)

theorem size_extract16 (d : Digest) : (d.bytes.extract 0 16).size = 16 := by
  simp [ByteArray.size_extract, d.size_eq]

/-- The slot of reader `x` holding tag `t`: 16 bytes of SHA-256("zrdtS3" ‖ x ‖ t). Binding `x`
means a tag shown by one account is useless to another. -/
def slotOf (x : Aci) (t : Digest) : Slot :=
  let d := sha256 ("zrdtS3".toUTF8 ++ x.bytes ++ t.bytes)
  ⟨d.bytes.extract 0 16, size_extract16 d⟩

def coreOf (g : GroupId) (commit : Digest) (author : Aci) : Digest :=
  sha256 ("zrdtC3".toUTF8 ++ g.bytes ++ commit.bytes ++ author.bytes)

/-- What any current member may hold: no author, no commitment. -/
structure Leaf where
  group : GroupId
  core : Digest
  links : Array Digest
  slots : Array Slot
deriving DecidableEq

def leafBytes (l : Leaf) : ByteArray :=
  "zrdt3".toUTF8 ++ l.group.bytes ++ l.core.bytes ++ u32be l.links.size ++ linksBytes' l.links ++
    u32be l.slots.size ++ l.slots.foldl (fun acc s => acc ++ s.bytes) .empty

/-- The record digest: the same for the leaf and the full record. -/
def hashLeaf (l : Leaf) : Digest := sha256 (leafBytes l)

/-- A full record: the leaf plus the opening of its core. -/
structure Full where
  leaf : Leaf
  commit : Digest
  author : Aci

/-- Honest construction at freeze time: one slot per addressee, from the pairwise keys the host
derived for exactly the accounts the send will address. -/
def build (g : GroupId) (commit : Digest) (links : Array Digest) (author : Aci)
    (keys : List (Aci × ByteArray)) : Full :=
  let core := coreOf g commit author
  ⟨⟨g, core, links, (keys.map fun (x, k) => slotOf x (tag k g author x core links)).toArray⟩,
    commit, author⟩

theorem build_addresses {g commit links author keys x k}
    (h : (x, k) ∈ keys) :
    slotOf x (tag k g author x (build g commit links author keys).leaf.core links) ∈
      (build g commit links author keys).leaf.slots := by
  simp only [build, List.mem_toArray, List.mem_map]
  exact ⟨(x, k), h, rfl⟩

/-! ## The responder (runs in zrdtd; the host sends the bytes it returns) -/

inductive Node
  | full (r : Full)
  | leaf (l : Leaf)

structure Item where
  digest : Digest
  /-- The requester's tag for this record, if it claims to be addressed. -/
  proof : Option Digest
  /-- The opening the host holds for this digest, if any. -/
  opening : Option ByteArray

inductive Out
  | unknown (d : Digest)
  | leaf (d : Digest) (l : Leaf)
  | opened (d : Digest) (r : Full) (opening : ByteArray)

def entitled (requester : Aci) (r : Full) (proof : Option Digest) : Bool :=
  r.author == requester ||
    match proof with
    | some t => r.leaf.slots.contains (slotOf requester t)
    | none => false

def respond1 (get : Digest → Option Node) (requester : Aci) (it : Item) : Out :=
  match get it.digest with
  | none => .unknown it.digest
  | some (.leaf l) => .leaf it.digest l
  | some (.full r) =>
    match it.opening with
    | some o =>
      if entitled requester r it.proof && openingMatches r.leaf.group r.author r.commit o then
        .opened it.digest r o
      else .leaf it.digest r.leaf
    | none => .leaf it.digest r.leaf

def respond (get : Digest → Option Node) (requester : Aci) (items : List Item) : List Out :=
  items.map (respond1 get requester)

/-- **No opening leaves zrdtd except to the record's author or to a requester whose slot is in
the record, and only an opening of that record's commitment.** -/
theorem respond_scoped {get : Digest → Option Node} {requester : Aci} {items : List Item}
    {d : Digest} {r : Full} {o : ByteArray}
    (h : Out.opened d r o ∈ respond get requester items) :
    get d = some (.full r) ∧
      (r.author = requester ∨
        ∃ it ∈ items, it.digest = d ∧ ∃ t, it.proof = some t ∧ slotOf requester t ∈ r.leaf.slots) ∧
      openingMatches r.leaf.group r.author r.commit o = true := by
  simp only [respond, List.mem_map] at h
  obtain ⟨it, hit, hout⟩ := h
  unfold respond1 at hout
  split at hout
  · cases hout
  · cases hout
  · rename_i r' hget
    split at hout
    · rename_i o' _
      split at hout
      · rename_i hc
        cases hout
        simp only [Bool.and_eq_true] at hc
        obtain ⟨he, hm⟩ := hc
        refine ⟨hget, ?_, hm⟩
        simp only [entitled, Bool.or_eq_true, beq_iff_eq] at he
        rcases he with ha | hs
        · exact Or.inl ha
        · right
          refine ⟨it, hit, rfl, ?_⟩
          split at hs
          · rename_i t ht
            exact ⟨t, ht, Array.contains_iff_mem.mp hs⟩
          · cases hs
      · cases hout
    · cases hout

/-! ## The newcomer's leaf check (runs in zrdtd with the pairwise keys the host derived) -/

inductive Verdict
  | badHash
  | addressedToYou (author : Aci) (t : Digest)
  | notForYou
deriving DecidableEq

def addressedTo (me : Aci) (cands : List (Aci × ByteArray)) (l : Leaf) : Option (Aci × Digest) :=
  cands.findSome? fun (a, k) =>
    let t := tag k l.group a me l.core l.links
    if l.slots.contains (slotOf me t) then some (a, t) else none

def leafVerdict (me : Aci) (cands : List (Aci × ByteArray)) (d : Digest) (l : Leaf) : Verdict :=
  if hashLeaf l ≠ d then .badHash
  else match addressedTo me cands l with
    | some (a, t) => .addressedToYou a t
    | none => .notForYou

theorem leafVerdict_notForYou {me cands d l} (h : leafVerdict me cands d l = .notForYou) :
    hashLeaf l = d ∧
      ∀ a k, (a, k) ∈ cands → slotOf me (tag k l.group a me l.core l.links) ∉ l.slots := by
  unfold leafVerdict at h
  split at h
  · cases h
  · rename_i hd
    refine ⟨Classical.not_not.mp hd, ?_⟩
    split at h
    · cases h
    · rename_i hn
      intro a k hak hmem
      have : (addressedTo me cands l).isSome := by
        unfold addressedTo
        rw [List.findSome?_isSome_iff]
        refine ⟨(a, k), hak, ?_⟩
        simp only
        rw [if_pos (Array.contains_iff_mem.mpr hmem)]
        rfl
      rw [hn] at this
      cases this

/-- **An honestly built record addressed to `me` can never be accepted as a leaf**, provided my
candidate keys include the author's pairwise key with me (X25519 is symmetric, so the key the
author used is the key I derive). -/
theorem addressed_never_leaf {g commit links author keys me k cands}
    (hk : (me, k) ∈ keys) (hc : (author, k) ∈ cands) :
    leafVerdict me cands (hashLeaf (build g commit links author keys).leaf)
      (build g commit links author keys).leaf ≠ .notForYou := by
  intro h
  have := (leafVerdict_notForYou h).2 author k hc
  exact this (build_addresses hk)

/-! ## Deniability, witness form: the reader can make anything his own check accepts -/

def copyVerified (me : Aci) (k : ByteArray) (r : Full) : Bool :=
  r.leaf.slots.contains (slotOf me (tag k r.leaf.group r.author me r.leaf.core r.leaf.links))

/-- Reader `x`, holding only the pairwise key `k` (which he derives from his own private key),
builds a record in `a`'s name that his own check accepts: a verifying tag is no evidence to
anyone but `x`. -/
theorem reader_can_forge (x a : Aci) (k : ByteArray) (g : GroupId) (commit : Digest)
    (links : Array Digest) : copyVerified x k (build g commit links a [(x, k)]) = true := by
  unfold copyVerified
  exact Array.contains_iff_mem.mpr (build_addresses (List.mem_singleton.mpr rfl))

/-! ## Two-level digest: a leaf that hashes to a record's digest is that record's leaf, or there
is a SHA-256 collision (given the encoding is injective, as `encode_injective` is for zrdt2). -/

theorem leaf_sound (hinj : Function.Injective leafBytes) {l l' : Leaf}
    (h : hashLeaf l = hashLeaf l') :
    l = l' ∨ ∃ x y, x ≠ y ∧ sha256 x = sha256 y := by
  by_cases he : l = l'
  · exact Or.inl he
  · exact Or.inr ⟨leafBytes l, leafBytes l', fun hb => he (hinj hb), h⟩

/-- The core hides who wrote it: two openings of the same core are equal or collide. -/
theorem core_sound {g g' : GroupId} {c c' : Digest} {a a' : Aci}
    (hinj : ∀ (g : GroupId) (c : Digest) (a : Aci) (g' : GroupId) (c' : Digest) (a' : Aci), ("zrdtC3".toUTF8 ++ g.bytes ++ c.bytes ++ a.bytes) =
      ("zrdtC3".toUTF8 ++ g'.bytes ++ c'.bytes ++ a'.bytes) → g = g' ∧ c = c' ∧ a = a')
    (h : coreOf g c a = coreOf g' c' a') :
    (g = g' ∧ c = c' ∧ a = a') ∨ ∃ x y, x ≠ y ∧ sha256 x = sha256 y := by
  by_cases he : ("zrdtC3".toUTF8 ++ g.bytes ++ c.bytes ++ a.bytes) =
      ("zrdtC3".toUTF8 ++ g'.bytes ++ c'.bytes ++ a'.bytes)
  · exact Or.inl (hinj _ _ _ _ _ _ he)
  · exact Or.inr ⟨_, _, he, h⟩

/-! ## A run on real bytes -/

namespace Ex
def g : GroupId := ⟨⟨Array.replicate 32 0x67⟩, rfl⟩
def alice : Aci := ⟨⟨Array.replicate 16 0xa1⟩, rfl⟩
def bob : Aci := ⟨⟨Array.replicate 16 0xb0⟩, rfl⟩
def carol : Aci := ⟨⟨Array.replicate 16 0xc0⟩, rfl⟩
def newcomer : Aci := ⟨⟨Array.replicate 16 0xee⟩, rfl⟩
-- Stand-ins for HKDF(X25519(..)) outputs.
def kAB : ByteArray := pairKey ⟨Array.replicate 32 1⟩ g
def kAC : ByteArray := pairKey ⟨Array.replicate 32 2⟩ g
def kAN : ByteArray := pairKey ⟨Array.replicate 32 3⟩ g
def nonce : Nonce := ⟨⟨Array.replicate 32 0x4e⟩, rfl⟩
def msg : ByteArray := ⟨#[0x0a, 5]⟩ ++ "hello".toUTF8
def opening : ByteArray := nonce.bytes ++ msg
def cmt : Digest := (Zrdt.commit g alice nonce msg).get!
/-- Alice writes before the newcomer joined: addressed to Bob and Carol only. -/
def r : Full := build g cmt #[] alice [(bob, kAB), (carol, kAC)]
def d : Digest := hashLeaf r.leaf
def get (x : Digest) : Option Node := if x = d then some (.full r) else none
def tB : Digest := tag kAB g alice bob r.leaf.core #[]
def tN : Digest := tag kAN g alice newcomer r.leaf.core #[]
end Ex

open Ex in
#guard openingMatches g alice cmt opening
-- Bob, addressed, presenting his tag: gets the opening.
open Ex in
#guard match respond get bob [⟨d, some tB, some opening⟩] with
  | [.opened ..] => true | _ => false
-- The newcomer presenting the tag he can compute: leaf only.
open Ex in
#guard match respond get newcomer [⟨d, some tN, some opening⟩] with
  | [.leaf ..] => true | _ => false
-- The newcomer replaying Bob's tag under his own ACI: leaf only (slot binds the ACI).
open Ex in
#guard match respond get newcomer [⟨d, some tB, some opening⟩] with
  | [.leaf ..] => true | _ => false
-- Bob with the wrong opening (another message): leaf only.
open Ex in
#guard match respond get bob [⟨d, some tB, some (nonce.bytes ++ "x".toUTF8)⟩] with
  | [.leaf ..] => true | _ => false
-- Newcomer's leaf check: not for him. Bob's: addressed to him, with the author and the tag.
open Ex in
#guard leafVerdict newcomer [(alice, kAN)] d r.leaf == .notForYou
open Ex in
#guard leafVerdict bob [(carol, kAC), (alice, kAB)] d r.leaf == .addressedToYou alice tB
open Ex in
#guard leafVerdict bob [(alice, kAB)] Digest.zero r.leaf == .badHash

end Zrdt.Dvs

#print axioms Zrdt.Dvs.respond_scoped
#print axioms Zrdt.Dvs.leafVerdict_notForYou
#print axioms Zrdt.Dvs.addressed_never_leaf
#print axioms Zrdt.Dvs.reader_can_forge
#print axioms Zrdt.Dvs.leaf_sound
