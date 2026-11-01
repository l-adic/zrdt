import Zrdt.Digest
import Std.Data.TreeSet

/-!
# Records

A record (`Rec`) is one message's entry in a chat's history. It holds:

- `group`: the chat (Signal group) it belongs to;
- `commit`: the commitment to the message content (docs/PLAN.md §3.4);
- `links`: the digests of the messages its sender had as heads when sending;
- `author`: the sender's account id.

The links are kept in one canonical form: sorted increasing, with no digest twice
(`StrictlySorted`). A `Rec` carries a proof of this, so a record with links out of order or
repeated cannot exist. Then two records that differ only in link order cannot be told apart by
`==` but hash differently: that case is ruled out by the type.

Records are built by `Rec.make`, which sorts and removes duplicates, or by the strict decoder in
`Zrdt.Encode`, which rejects links that are not already canonical.

The record's digest, `hashRecord r := sha256 (encode r)`, is in `Zrdt.Encode`, because it needs
the encoder.
-/

namespace Zrdt

/-! ## Canonical link lists -/

/-- `StrictlySorted ds`: every digest is smaller than every later one. So the digests are in
increasing order and none appears twice. -/
def StrictlySorted (ds : Array Digest) : Prop :=
  ds.toList.Pairwise (fun a b => compare a b = .lt)

/-- Check that each digest in the list is smaller than the next one. -/
def isStrictlySortedList : List Digest → Bool
  | a :: b :: rest => compare a b == .lt && isStrictlySortedList (b :: rest)
  | _ => true

/-- Comparing neighbours is enough, because the order is transitive. -/
theorem isStrictlySortedList_iff :
    ∀ l : List Digest, isStrictlySortedList l = true ↔ l.Pairwise (fun a b => compare a b = .lt)
  | [] => by simp [isStrictlySortedList]
  | [a] => by simp [isStrictlySortedList]
  | a :: b :: rest => by
    simp only [isStrictlySortedList, Bool.and_eq_true, beq_iff_eq,
      isStrictlySortedList_iff (b :: rest)]
    constructor
    · rintro ⟨hab, hrest⟩
      refine List.Pairwise.cons ?_ hrest
      intro c hc
      cases hc with
      | head => exact hab
      | tail _ hc => exact Std.TransCmp.lt_trans hab (List.rel_of_pairwise_cons hrest hc)
    · intro h
      exact ⟨List.rel_of_pairwise_cons h List.mem_cons_self, h.of_cons⟩

instance (ds : Array Digest) : Decidable (StrictlySorted ds) :=
  decidable_of_iff _ (isStrictlySortedList_iff ds.toList)

/-- Sort digests increasing and drop repeats. -/
def canonicalLinks (ds : Array Digest) : Array Digest :=
  (Std.TreeSet.ofList ds.toList compare).toArray

/-- `canonicalLinks` really is canonical. -/
theorem canonicalLinks_sorted (ds : Array Digest) : StrictlySorted (canonicalLinks ds) := by
  unfold StrictlySorted canonicalLinks
  rw [Std.TreeSet.toList_toArray]
  exact Std.TreeSet.ordered_toList

/-- `canonicalLinks` keeps exactly the digests it was given. -/
@[simp] theorem mem_canonicalLinks {d : Digest} {ds : Array Digest} :
    d ∈ canonicalLinks ds ↔ d ∈ ds := by
  simp [canonicalLinks]

/-! ## `Rec` -/

/-- One message's entry in the chat history: its chat, the commitment to its content, the
digests it links to (canonical: increasing, no repeats), and its author. -/
structure Rec where
  /-- The chat (Signal group) the record belongs to. -/
  group : GroupId
  /-- The commitment to the message content (docs/PLAN.md §3.4). -/
  commit : Digest
  /-- The digests of the records the sender had as heads, increasing, no repeats. -/
  links : Array Digest
  /-- The sender's account id. -/
  author : Aci
  /-- The links are canonical. -/
  links_sorted : StrictlySorted links
deriving DecidableEq

namespace Rec

/-- Build a record from links in any order, possibly repeated: they are sorted and repeats are
dropped. This is the way to make a record from data. -/
def make (group : GroupId) (commit : Digest) (links : Array Digest) (author : Aci) : Rec :=
  ⟨group, commit, canonicalLinks links, author, canonicalLinks_sorted links⟩

/-- `make` keeps exactly the given links. -/
@[simp] theorem mem_links_make {g : GroupId} {c : Digest} {ls : Array Digest} {a : Aci}
    {d : Digest} : d ∈ (make g c ls a).links ↔ d ∈ ls :=
  mem_canonicalLinks

@[simp] theorem group_make {g c ls a} : (make g c ls a).group = g := rfl
@[simp] theorem commit_make {g c ls a} : (make g c ls a).commit = c := rfl
@[simp] theorem author_make {g c ls a} : (make g c ls a).author = a := rfl

/-- Two records are equal when their four data fields are (the proof field carries no data). -/
@[ext] theorem ext {r s : Rec} (hg : r.group = s.group) (hc : r.commit = s.commit)
    (hl : r.links = s.links) (ha : r.author = s.author) : r = s := by
  cases r; cases s; cases hg; cases hc; cases hl; cases ha; rfl

instance : Repr Rec where
  reprPrec r _ :=
    "{ group := " ++ repr r.group ++ ", commit := " ++ repr r.commit ++ ", links := " ++
      repr r.links ++ ", author := " ++ repr r.author ++ " }"

end Rec

/-! ## Example values

Used by the examples here and in `Zrdt.Encode`. -/

namespace Examples

/-- The digest whose 32 bytes all equal `n`. -/
def dig (n : UInt8) : Digest := ⟨⟨Array.replicate 32 n⟩, rfl⟩

/-- An example group id. -/
def group : GroupId := ⟨⟨Array.replicate 32 0x67⟩, rfl⟩

/-- Another group id. -/
def otherGroup : GroupId := ⟨⟨Array.replicate 32 0x68⟩, rfl⟩

/-- An example author. -/
def alice : Aci := ⟨⟨Array.replicate 16 0xa1⟩, rfl⟩

/-- A first message: no links. -/
def first : Rec := Rec.make group (dig 0xc0) #[] alice

/-- A message given links out of order and repeated. -/
def reply : Rec := Rec.make group (dig 0xc1) #[dig 3, dig 1, dig 3, dig 2] alice

end Examples

open Examples in
#guard reply.links == #[dig 1, dig 2, dig 3]
open Examples in
#guard Rec.make group (dig 0xc1) #[dig 1, dig 2, dig 3] alice == reply
open Examples in
#guard first.links.isEmpty
open Examples in
#guard first != reply

open Examples in
example : StrictlySorted #[dig 1, dig 2] := by decide +kernel
open Examples in
example : ¬ StrictlySorted #[dig 2, dig 1] := by decide +kernel
open Examples in
example : ¬ StrictlySorted #[dig 1, dig 1] := by decide +kernel

end Zrdt
