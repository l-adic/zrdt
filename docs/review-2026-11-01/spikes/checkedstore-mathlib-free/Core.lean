import Std.Data.HashMap
import Std.Data.HashSet
/-! Option 1 scratch: a Mathlib-free `Built` next to the code (imports Init/Std only). -/
namespace Zrdt

/-- 32-byte digest. `Vector UInt8 32` gets core's lawful lexicographic `Ord`
(`TransOrd`, `LawfulEqOrd` in `Init/Data/Ord/Vector.lean`). -/
abbrev Digest := Vector UInt8 32
instance : Hashable Digest := ⟨fun v => hash v.toArray⟩

structure Payload where
  group : Digest
  timestamp : UInt64
  body : ByteArray
deriving DecidableEq

/-- Implementation record: links as an `Array` (canonicity is a separate invariant). -/
structure Rec where
  payload : Payload
  links : Array Digest
  author : Digest
deriving DecidableEq

/-- Stand-in for `sha256 ∘ encode`; the proofs never unfold it. -/
opaque hashRecord : Rec → Digest

structure RawStore where
  group : Digest
  map : Std.HashMap Digest Rec
  heads : Std.HashSet Digest

/-- Newest-first accept order: each record's links are hashes of strictly older records. -/
inductive Ordered : List Rec → Prop
  | nil : Ordered []
  | cons {r : Rec} {rs : List Rec} :
      (∀ d ∈ r.links, ∃ r' ∈ rs, hashRecord r' = d) → Ordered rs → Ordered (r :: rs)

/-- Mathlib-free certificate (claim C2, option 1). -/
structure Built (c : RawStore) : Prop where
  keys : ∀ (k : Digest) (r : Rec), c.map[k]? = some r → hashRecord r = k
  chat : ∀ (k : Digest) (r : Rec), c.map[k]? = some r → r.payload.group = c.group
  heads : ∀ d, d ∈ c.heads ↔ (d ∈ c.map ∧ ∀ (k : Digest) (r : Rec), c.map[k]? = some r → d ∉ r.links)
  order : ∃ l, Ordered l ∧ ∀ r, r ∈ l ↔ ∃ k : Digest, c.map[k]? = some r

structure CheckedStore where
  raw : RawStore
  built : Built raw

def CheckedStore.empty (g : Digest) : CheckedStore where
  raw := ⟨g, ∅, ∅⟩
  built := {
    keys := by simp
    chat := by simp
    heads := by simp
    order := ⟨[], .nil, by simp⟩ }

inductive AcceptResult
  | accepted (d : Digest) | missing (ds : List Digest) | collision (d : Digest) | wrongChat

/-- The raw operation (what option 2 would export as-is). -/
def rawAccept (c : RawStore) (r : Rec) : AcceptResult × RawStore :=
  if r.payload.group ≠ c.group then (.wrongChat, c) else
  let d := hashRecord r
  match c.map[d]? with
  | some r' => if r' = r then (.accepted d, c) else (.collision d, c)
  | none =>
    let missing := r.links.toList.filter (fun l => !c.map.contains l)
    if missing.isEmpty then
      (.accepted d, { c with map := c.map.insert d r,
                             heads := (c.heads.filter (fun h => !r.links.contains h)).insert d })
    else (.missing missing, c)

end Zrdt
