-- PORTED (2026-11-01, branch join-core): these tests (as `#guard`s and kernel-checked examples) now live in core/Zrdt/Serve.lean
-- (frame ops in core/Zrdt/Proto.lean, protocol 3), greenfield: field 201 is required, so the
-- zrdtSentTo path and the legacy tests below are gone there. This file is kept only as the
-- review-round-1 reference; do not build on it.
-- Reference copy from the JOIN_PLAN v2 review, revised after review round 1 (2026-11-01). Not
-- built by any lake target. Checked with `lake env lean` against core/ at a079b3e, placed under
-- core/Scratch/. No sorry.
import Scratch.Serve
open Zrdt Zrdt.Serve Zrdt.Examples

def dave : Aci := ⟨⟨Array.replicate 16 0xd4⟩, rfl⟩
def eve : Aci := ⟨⟨Array.replicate 16 0xe5⟩, rfl⟩
def mallory : Aci := ⟨⟨Array.replicate 16 0xee⟩, rfl⟩

/-- Identity keys, 33 bytes serialized. `keyBob'` is a key the server swapped in for Bob. -/
def key (n : UInt8) : ByteArray := ⟨Array.replicate 33 n⟩
def keyAlice := key 1
def keyBob := key 2
def keyCarol := key 3
def keyEve := key 5
def keyMallory := key 6
def keyBob' := key 0x99
def keyCarol' := key 0x98

def nonceOf (n : UInt8) : Nonce := ⟨⟨Array.replicate 32 n⟩, rfl⟩
def tagBytes (k : Option ByteArray) : ByteArray :=
  match k with
  | some k => ⟨keyTag k⟩
  | none => ⟨zeroTag⟩
/-- Field 201, wire type 2 (key varint 0xca 0x0c): entries aci ‖ tag, increasing by aci. `none`
is the zero tag (a member Signal does not send to). -/
def varint (n : Nat) : ByteArray :=
  if n < 128 then bytesOf [n] else bytesOf [n % 128 + 128, n / 128]
def audField (es : List (Aci × Option ByteArray)) : ByteArray :=
  let payload := es.foldl (fun b (a, k) => b ++ a.bytes ++ tagBytes k) ByteArray.empty
  bytesOf [0xca, 0x0c] ++ varint payload.size ++ payload
def body (s : String) : ByteArray := bytesOf [0x0a, s.utf8ByteSize] ++ s.toUTF8
def masterKeyField : ByteArray := bytesOf [0x7a, 34, 0x0a, 32] ++ ⟨Array.replicate 32 0x4b⟩
def msg (s : String) (es : List (Aci × Option ByteArray)) : ByteArray :=
  body s ++ masterKeyField ++ audField es
/-- A disappearing message: field 5 (expireTimer) = 60. -/
def msgTimer (s : String) (es : List (Aci × Option ByteArray)) : ByteArray :=
  msg s es ++ bytesOf [0x28, 60]

/-- (record, opening) of message `m` by `a` with links `ls`. -/
def mkMsg (a : Aci) (n : UInt8) (m : ByteArray) (ls : Array Digest) : Rec × ByteArray :=
  match commitWithOpening group a (nonceOf n) m with
  | some (c, o) => (Rec.make group c ls a, o)
  | none => (Rec.make group Digest.zero ls a, ByteArray.empty)
def mk (a : Aci) (n : UInt8) (s : String) (es : List (Aci × Option ByteArray))
    (ls : Array Digest) : Rec × ByteArray :=
  mkMsg a n (msg s es) ls

def AC := [(alice, some keyAlice), (carol, some keyCarol)]
def ABC := [(alice, some keyAlice), (bob, some keyBob), (carol, some keyCarol)]

-- p: Carol, before Bob joined. q: Alice, after (Bob addressed). x: Carol with a stale view
-- (Bob not addressed) linking q. y: Alice, addressed to Bob, linking x.
def p := mk carol 1 "pre-join secret" AC #[]
def q := mk alice 2 "welcome bob" ABC #[hashRecord p.1]
def x := mk carol 3 "stale view" AC #[hashRecord q.1]
def y := mk alice 4 "later" ABC #[hashRecord x.1]
def store : CheckedStore := ((CheckedStore.empty group).acceptAll #[p.1, q.1, x.1, y.1]).1
def heldOf (l : List (Rec × ByteArray)) : Std.ExtTreeMap Digest Held compare :=
  Std.ExtTreeMap.ofList (l.map fun (r, o) => (hashRecord r, ({ opening := some o } : Held))) compare
def held := heldOf [p, q, x, y]

/-- Requester `a` as this device holds it, with key `k`. -/
def rq (a : Aci) (k : ByteArray) (since : Array Digest := #[]) (wanted : Option (Array Digest) := none)
    (forExport := false) : Query :=
  { aci := a, key := k, since, wanted, forExport }
/-- Responder Alice, closed store, holding her own records as `live`. -/
def meAlice : Me := { aci := alice, live := Std.ExtTreeSet.ofList [hashRecord q.1, hashRecord y.1] }

/-- The records whose content went out. -/
def contentOf (es : List Entry) : List Rec :=
  es.filterMap fun | .addressed r (some _) _ => some r | _ => none
def showE : Entry → String
  | .addressed r o ac => s!"addressed by-alice={r.author == alice} content={o.isSome} authorCopy={ac}"
  | .after r => s!"after by-carol={r.author == carol}"
  | .boundary d => s!"boundary p={d == hashRecord p.1}"

-- the opening keeps field 201 and drops field 15
#guard (audienceOf p.2).map (·.map (·.aci)) == some #[alice, carol]
#guard (openingMatches group carol p.1.commit p.2)
#guard store.size == 4

#eval (serve store.raw meAlice held (rq bob keyBob)).map showE
-- Bob never gets p's content; p goes to him as a boundary digest only.
#guard !(contentOf (serve store.raw meAlice held (rq bob keyBob))).contains p.1
#guard (serve store.raw meAlice held (rq bob keyBob)).any fun
  | .boundary d => d == hashRecord p.1 | _ => false
-- Carol's stale-view record goes to Bob as structure (`after`), never content.
#guard (serve store.raw meAlice held (rq bob keyBob)).any fun
  | .after r => r == x.1 | _ => false
-- Carol (author of p, seated with her own key) gets p's content.
#guard (contentOf (serve store.raw meAlice held (rq carol keyCarol))).contains p.1
-- Round 1: no author shortcut. Carol under a swapped key gets nothing, not even her own records.
#guard contentOf (serve store.raw meAlice held (rq carol keyCarol')) == []
-- Round 1: a requester whose identity key changed gets no content.
#guard contentOf (serve store.raw meAlice held (rq bob keyBob')) == []
-- Round 1: Alice's own records go out as author copies; Carol's do not.
#guard (serve store.raw meAlice held (rq bob keyBob)).all fun
  | .addressed r _ ac => ac == (r.author == alice) | _ => true

-- A relayer rewrites p's audience to include Bob, keeping the nonce: the opening no longer
-- matches p's commit, so it is never served.
def forgedOpening : ByteArray :=
  match commitWithOpening group carol (nonceOf 1) (msg "pre-join secret" ABC) with
  | some (_, o) => o | none => ByteArray.empty
#guard !(openingMatches group carol p.1.commit forgedOpening)
#guard !(serveOpening meAlice (rq bob keyBob) (hashRecord p.1) p.1 forgedOpening)
def heldBad := held.insert (hashRecord p.1) { opening := some forgedOpening }
#guard !(contentOf (serve store.raw meAlice heldBad (rq bob keyBob))).contains p.1

-- Round 1, pre-upgrade history: l has no field 201. Its author Alice serves it to the accounts
-- her `zrdtSentTo` lists (under the keys recorded then); Carol, who holds the same opening, serves
-- no one; Alice serves no one once the record is not hers-and-live.
def l := mkMsg alice 14 (body "before the upgrade" ++ masterKeyField) #[]
def storeL : CheckedStore := ((CheckedStore.empty group).acceptAll #[l.1]).1
def sentToL : Array Seat := #[⟨alice, keyTag keyAlice⟩, ⟨bob, keyTag keyBob⟩]
def meAliceL : Me :=
  { aci := alice, live := Std.ExtTreeSet.ofList [hashRecord l.1],
    sentTo := Std.ExtTreeMap.ofList [(hashRecord l.1, sentToL)] compare }
#guard audienceOf l.2 == none
#guard contentOf (serve storeL.raw meAliceL (heldOf [l]) (rq bob keyBob)) == [l.1]
#guard contentOf (serve storeL.raw meAliceL (heldOf [l]) (rq bob keyBob')) == []
#guard contentOf (serve storeL.raw meAliceL (heldOf [l]) (rq carol keyCarol)) == []
def meCarolL : Me :=
  { aci := carol, sentTo := Std.ExtTreeMap.ofList [(hashRecord l.1, sentToL)] compare }
#guard contentOf (serve storeL.raw meCarolL (heldOf [l]) (rq bob keyBob)) == []
#guard contentOf (serve storeL.raw { meAliceL with live := ∅ } (heldOf [l]) (rq bob keyBob)) == []

-- Round 1: blocked Mallory is in the audience with the zero tag: seated nowhere, gets nothing.
def m1 := mk alice 7 "not for mallory"
  [(alice, some keyAlice), (bob, some keyBob), (mallory, none)] #[]
def storeM : CheckedStore := ((CheckedStore.empty group).acceptAll #[m1.1]).1
#guard contentOf (serve storeM.raw meAlice (heldOf [m1]) (rq mallory keyMallory)) == []
#guard contentOf (serve storeM.raw meAlice (heldOf [m1]) (rq bob keyBob)) == [m1.1]

-- Round 1: a forgery f "by Alice", relayed to Alice by Mallory (A8: she accepts and disowns it),
-- seats Bob. Alice serves its content to Bob (its own audience seats him), but never as an author
-- copy: her provenance for f is not live, and she disowned it.
def f := mk alice 8 "forged in alice's name" ABC #[]
def storeF : CheckedStore := ((CheckedStore.empty group).acceptAll #[f.1]).1
def meAliceF : Me := { aci := alice, disown := Std.ExtTreeSet.ofList [hashRecord f.1] }
#guard (serve storeF.raw meAliceF (heldOf [f]) (rq bob keyBob)).all fun
  | .addressed _ _ ac => !ac | _ => true

-- Round 1: an export refuses a disappearing message; a relay still carries it.
def t := mkMsg alice 9 (msgTimer "disappears" ABC) #[]
def storeT : CheckedStore := ((CheckedStore.empty group).acceptAll #[t.1]).1
#guard ephemeral t.2
#guard !ephemeral q.2
#guard contentOf (serve storeT.raw meAlice (heldOf [t]) (rq bob keyBob (forExport := true))) == []
#guard contentOf (serve storeT.raw meAlice (heldOf [t]) (rq bob keyBob)) == [t.1]

-- Round 1, re-add: ra1 (Bob addressed), Bob removed, gap rg1 (Carol, Bob not addressed), Bob
-- re-added, ra2 (Bob addressed). With `since` = his old heads, the gap comes back as a digest;
-- without it, as an `after` structure (metadata about the gap, never content).
def ra1 := mk alice 10 "before removal" ABC #[]
def rg1 := mk carol 11 "while bob was out" AC #[hashRecord ra1.1]
def ra2 := mk alice 12 "after re-add" ABC #[hashRecord rg1.1]
def storeR : CheckedStore := ((CheckedStore.empty group).acceptAll #[ra1.1, rg1.1, ra2.1]).1
def heldR := heldOf [ra1, rg1, ra2]
#guard (serve storeR.raw meAlice heldR (rq bob keyBob (since := #[hashRecord ra1.1]))).all fun
  | .after _ => false | _ => true
#guard (serve storeR.raw meAlice heldR (rq bob keyBob)).any fun
  | .after r => r == rg1.1 | _ => false
-- `since` shapes structure, never content: a per-digest repair of ra1 returns ra1's content even
-- when ra1 is in `since` (Bob was sent ra1 and missed it), and no gap structure.
#guard contentOf (serve storeR.raw meAlice heldR
  (rq bob keyBob (since := #[hashRecord ra1.1]) (wanted := some #[hashRecord ra1.1]))) == [ra1.1]
-- A per-digest request for the gap record gives Bob its digest only.
#guard (serve storeR.raw meAlice heldR
    (rq bob keyBob (since := #[hashRecord ra1.1]) (wanted := some #[hashRecord rg1.1]))).all fun
  | .boundary _ => true | _ => false

-- Round 1, crawl attempts by the newcomer: every since/wanted shape returns no content for p
-- and no structure of p.
def crawls : List Query :=
  [rq bob keyBob, rq bob keyBob (wanted := some #[hashRecord p.1]),
   rq bob keyBob (since := #[hashRecord y.1]), rq bob keyBob (since := #[hashRecord p.1]),
   rq bob keyBob (wanted := some #[hashRecord p.1, hashRecord q.1, hashRecord x.1])]
#guard crawls.all fun cq => (serve store.raw meAlice held cq).all fun
  | .addressed r o _ => r != p.1 && (o.isNone || r != p.1)
  | .after r => r != p.1
  | .boundary _ => true

-- Round 1, H3 regression. v1 served an opening when the record's revision was at least the
-- requester's join revision as the server reported it. Carol's x was written at revision 8; the
-- server says Bob joined at 5 (he joined at 9). v1 releases x; `serve` does not.
def v1Serves (rev joinRev : Nat) : Bool := rev ≥ joinRev
#guard v1Serves 8 5
#guard !(contentOf (serve store.raw meAlice held (rq bob keyBob))).contains x.1

/-! Round 1, a second-generation newcomer. Bob caught up from Alice: he holds q, x, y in full
and p as a boundary digest. Carol, with a stale view (she never got q), writes w after Eve
joined, linking p; Bob accepts w relative to his boundary. Eve asks Bob. -/
def w := mk carol 13 "hi eve" [(alice, some keyAlice), (bob, some keyBob), (carol, some keyCarol),
  (eve, some keyEve)] #[hashRecord p.1]
def bobStore : RawStore :=
  { group, map := Std.ExtTreeMap.ofList ([q.1, x.1, y.1, w.1].map fun r => (hashRecord r, r)) compare,
    heads := Std.ExtTreeSet.ofList [hashRecord y.1, hashRecord w.1] }
def meBob : Me := { aci := bob, boundary := Std.ExtTreeSet.ofList [hashRecord p.1] }
def bobHeld := heldOf [q, y, w]

def entryDigest : Entry → Digest
  | .addressed r _ _ => hashRecord r | .after r => hashRecord r | .boundary d => d
def entryLinks : Entry → List Digest
  | .addressed r _ _ => r.links.toList | .after r => r.links.toList | .boundary _ => []
/-- Every link of a served record is a served record or a served boundary digest. -/
def closedView (es : List Entry) : Bool :=
  es.all fun e => (entryLinks e).all fun l => es.any (entryDigest · == l)
/-- The heads of a view: its digests that none of its records links. -/
def viewHeads (es : List Entry) : List Digest :=
  ((es.map entryDigest).filter fun d => !(es.any fun e => (entryLinks e).contains d)).mergeSort
    (fun a b => compare a b != .gt)
def bobHeads : List Digest := [hashRecord y.1, hashRecord w.1].mergeSort (fun a b => compare a b != .gt)

#eval (serve bobStore meBob bobHeld (rq eve keyEve)).map showE
-- Eve gets w's content, the rest as digests; the view is closed and has Bob's heads.
#guard contentOf (serve bobStore meBob bobHeld (rq eve keyEve)) == [w.1]
#guard closedView (serve bobStore meBob bobHeld (rq eve keyEve))
#guard viewHeads (serve bobStore meBob bobHeld (rq eve keyEve)) == bobHeads
-- Before round 1, the responder's own boundary was not served: Eve could not accept w.
#guard !closedView (serve bobStore { meBob with boundary := ∅ } bobHeld (rq eve keyEve))
