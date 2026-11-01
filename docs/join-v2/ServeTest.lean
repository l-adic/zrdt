-- Reference copy from the JOIN_PLAN v2 review (2026-11-01). Not built by any lake target.
-- Checked with `lake env lean` against core/ at af76d2f, placed under core/Scratch/. No sorry.
import Scratch.Serve
open Zrdt Zrdt.Serve Zrdt.Examples

def nonceOf (n : UInt8) : Nonce := ⟨⟨Array.replicate 32 n⟩, rfl⟩
/-- field 201, wire type 2: key varint 0xca 0x0c, then the packed ACIs. -/
def audField (as : List Aci) : ByteArray :=
  let payload := as.foldl (fun b a => b ++ a.bytes) ByteArray.empty
  bytesOf [0xca, 0x0c, payload.size] ++ payload
def body (s : String) : ByteArray := bytesOf [0x0a, s.utf8ByteSize] ++ s.toUTF8
def masterKeyField : ByteArray := bytesOf [0x7a, 34, 0x0a, 32] ++ ⟨Array.replicate 32 0x4b⟩
def msg (s : String) (as : List Aci) : ByteArray := body s ++ masterKeyField ++ audField as

/-- (record, opening) of a message by `a` with links `ls`. -/
def mk (a : Aci) (n : UInt8) (s : String) (as : List Aci) (ls : Array Digest) : Rec × ByteArray :=
  match commitWithOpening group a (nonceOf n) (msg s as) with
  | some (c, o) => (Rec.make group c ls a, o)
  | none => (Rec.make group Digest.zero ls a, ByteArray.empty)

-- p: Carol, before Bob joined. q: Alice, after (Bob addressed). x: Carol with a stale view
-- (Bob not addressed) linking q. y: Alice, addressed to Bob, linking x.
def p := mk carol 1 "pre-join secret" [alice, carol] #[]
def q := mk alice 2 "welcome bob" [alice, bob, carol] #[hashRecord p.1]
def x := mk carol 3 "stale view" [alice, carol] #[hashRecord q.1]
def y := mk alice 4 "later" [alice, bob, carol] #[hashRecord x.1]
def store : CheckedStore := ((CheckedStore.empty group).acceptAll #[p.1, q.1, x.1, y.1]).1
def held : Std.ExtTreeMap Digest Held compare :=
  Std.ExtTreeMap.ofList ([p, q, x, y].map fun (r, o) => (hashRecord r, ({ opening := some o } : Held))) compare

-- the opening keeps field 201 and drops field 15
#guard audienceOf p.2 == some #[alice, carol]
#guard (openingMatches group carol p.1.commit p.2)
#guard store.size == 4

def showE : Entry → String
  | .addressed r o _ => s!"addressed {r.author == alice} content={o.isSome}"
  | .after r => s!"after {r.author == carol}"
  | .boundary d => s!"boundary p={d == hashRecord p.1}"

#eval (serve store held bob).map showE
-- Carol (author of p) gets p's content; Bob never does.
#guard ((serve store held bob).filter fun | .addressed r (some _) _ => r == p.1 | _ => false).isEmpty
#guard ((serve store held carol).filter fun | .addressed r (some _) _ => r == p.1 | _ => false).length == 1
-- If Bob's held map says nothing about p (no opening, no audience), p is not even a boundary.
def held' := held.erase (hashRecord p.1)
#eval (serve store held' bob).map showE
-- A relayer rewrites p's audience to include Bob, keeping the nonce: the opening no longer
-- matches p's commit, so it is never served, and p's audience is treated as unknown.
def forgedOpening : ByteArray :=
  match commitWithOpening group carol (nonceOf 1) (msg "pre-join secret" [alice, bob, carol]) with
  | some (_, o) => o | none => ByteArray.empty
#guard !(openingMatches group carol p.1.commit forgedOpening)
#guard !(serveOpening bob p.1 forgedOpening)
def heldBad := held.insert (hashRecord p.1) { opening := some forgedOpening }
#guard ((serve store heldBad bob).filter fun | .addressed r _ _ => r == p.1 | _ => false).isEmpty
#eval (serve store heldBad bob).map showE
