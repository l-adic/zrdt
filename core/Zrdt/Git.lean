import Zrdt.AppBase

/-!
# Git (docs/apps/BUILD_M1.md §B.7, §C.3)

**Owner: lane git.** Ops `0x28`-`0x2F`: `GIT_PREPARE` `0x28`, `GIT_OBJECTS` `0x29`, `GIT_VIEW`
`0x2A`; `0x2B`-`0x2F` reserved. The git ops only read the daemon's state (`run` returns no new
state): a push's piece store is created and filled by lane base's ops, after the push record is
accepted into the channel. Byte layouts: `Proto.lean`, section `[lane git]`.

This module holds, without Mathlib:

- **raw objects** (`Kind`, `rawOf`, `parseRaw`, `Obj`): a SHA-256 repository's objects in their
  canonical form `<type> SP <decimal length> NUL <content>`, commit, tree and blob only. An
  object's id is SHA-256 of its raw form, so `zrdtd` recomputes every id with the SHA-256 it ships
  and needs no zlib, pack or idx;
- **`checkObjects`**: a push's stream (raw objects, concatenated, ids strictly increasing) cut into
  objects, each id recomputed, each tree and commit read by the allow-list grammar of BUILD_M1
  §B.7 (`parseTree`, `parseCommit`; the trusted object parser of BUILD_M1 §H);
- **the push body** (`Body`, `writeBody`, `parseBody`): field 212 of a git record, `"zgit1"`,
  canonical (`parseBody` takes only bytes `writeBody` writes back identically);
- **the table** (`Table`, `tableOf`): the git records of a channel store whose held opening
  matches them, read from their openings;
- **the pusher's checks** (`prepare`): limits and names, the root rule (G-F1), freshness (G-M6),
  the gate and the name rule (G-M1), exact shares (G-M7), and the message to commit;
- **the view** (`gitView`): the push log and the live branch values (a multi-value register);
- the ops (`Request`, `Reply`, `parse`, `run`) and the theorems of BUILD_M1 §C.3 that need no
  Mathlib. `refs_agree` and `force_visible` are in `Crdt/Merkle/Api.lean` (Part 6c), with their
  proofs in `Crdt/Merkle/AppsGit.lean`.
-/

namespace Zrdt.Git

open AppBase

/-! ## Constants -/

/-- A git object id: SHA-256 of the raw object, a SHA-256 repository's object id. -/
abbrev Oid := Digest

/-- At most 512 objects per push. -/
def maxObjects : Nat := 512
/-- At most 16 ref updates per push. -/
def maxUpdates : Nat := 16
/-- A ref name is 1 to 250 bytes. -/
def maxRefName : Nat := 250
/-- A repository name is 1 to 64 bytes. -/
def maxRepoName : Nat := 64
/-- The id in a `BAD_OBJECTS` reply when there is none. -/
def zeroOid : Oid := Digest.zero

/-! ## Raw objects -/

/-- The kinds of object M1 carries. A tag object is refused (`KIND`). -/
inductive Kind
  | commit
  | tree
  | blob
deriving DecidableEq, Repr

/-- The type word of each kind, as bytes. -/
def Kind.word : Kind → List UInt8
  | .commit => [0x63, 0x6f, 0x6d, 0x6d, 0x69, 0x74]
  | .tree => [0x74, 0x72, 0x65, 0x65]
  | .blob => [0x62, 0x6c, 0x6f, 0x62]

/-- The type word of a tag object (refused). -/
def tagWord : List UInt8 := [0x74, 0x61, 0x67]

#guard Kind.commit.word.toArray == "commit".toUTF8.data && Kind.tree.word.toArray == "tree".toUTF8.data &&
  Kind.blob.word.toArray == "blob".toUTF8.data && tagWord.toArray == "tag".toUTF8.data

/-- The kind byte of a `GIT_OBJECTS` reply: 1 commit, 2 tree, 3 blob. -/
def Kind.byte : Kind → UInt8
  | .commit => 1
  | .tree => 2
  | .blob => 3

/-- The decimal digits of `n`, most significant first, with no leading zero (`"0"` for 0). -/
def decDigits (n : Nat) : List UInt8 :=
  if n < 10 then [(48 + n).toUInt8] else decDigits (n / 10) ++ [(48 + n % 10).toUInt8]
termination_by n
decreasing_by omega

/-- The value of decimal digits. -/
def decValue (ds : List UInt8) : Nat := ds.foldl (fun acc c => acc * 10 + (c.toNat - 48)) 0

/-- A decimal digit. -/
def isDigit (c : UInt8) : Bool := 48 ≤ c && c ≤ 57

/-- A canonical decimal number: at least one digit, digits only, no leading zero. -/
def validDec (ds : List UInt8) : Bool :=
  !ds.isEmpty && ds.all isDigit && (ds.length == 1 || ds.head? != some 48)

#guard decDigits 0 == [48] && decDigits 1234 == [49, 50, 51, 52] && decValue [49, 50, 51, 52] == 1234
#guard validDec [48] && validDec [49, 48] && !validDec [48, 49] && !validDec [] && !validDec [0x61]

/-- The header of a raw object of kind `k` and length `n`: type word, space, decimal length, NUL. -/
def headerL (k : Kind) (n : Nat) : List UInt8 := k.word ++ 32 :: (decDigits n ++ [0])

/-- The raw form of an object: `<type> SP <decimal length> NUL <content>`. Its SHA-256 is the
object's id in a SHA-256 repository. -/
def rawOf (k : Kind) (c : ByteArray) : ByteArray := ⟨(headerL k c.size).toArray⟩ ++ c

/-- The bytes before the first `b`, and the bytes after it. -/
def splitAt? (b : UInt8) : List UInt8 → Option (List UInt8 × List UInt8)
  | [] => none
  | x :: xs => if x = b then some ([], xs) else (splitAt? b xs).map fun (p, q) => (x :: p, q)

/-- Why `checkObjects` (and `GIT_PREPARE`'s other object checks) refuse: the reason byte of
`BAD_OBJECTS`. -/
inductive ObjReason
  /-- 1: an object that cannot be read, a malformed tree, or an unknown type. -/
  | malformed
  /-- 2: a tag object. -/
  | kind
  /-- 3: a tree entry of mode 160000 (a gitlink). -/
  | gitlink
  /-- 4: a commit whose header is not on the allow-list. -/
  | header
  /-- 5: the stream's ids are not strictly increasing. -/
  | order
  /-- 6: more than 512 objects or 16 updates, or a body over the limits. -/
  | limits
  /-- 7: a repository or ref name that is not valid. -/
  | name
  /-- 8: the update list is not valid (a name twice, an update with neither value, a delete in a
  share), or the stream's ids are not the push's listed ids. -/
  | list
deriving DecidableEq, Repr

/-- The reason byte. -/
def ObjReason.byte : ObjReason → UInt8
  | .malformed => 1 | .kind => 2 | .gitlink => 3 | .header => 4 | .order => 5 | .limits => 6
  | .name => 7 | .list => 8

/-- The kind named by a type word. -/
def kindOfWord (w : List UInt8) : Except ObjReason Kind :=
  if w = Kind.commit.word then .ok .commit
  else if w = Kind.tree.word then .ok .tree
  else if w = Kind.blob.word then .ok .blob
  else if w = tagWord then .error .kind
  else .error .malformed

/-- Read a raw object's header from the front of `l`: its kind, its length, and the header's
size. -/
def parseHeaderL (l : List UInt8) : Except ObjReason (Kind × Nat × Nat) :=
  match splitAt? 32 l with
  | none => .error .malformed
  | some (w, rest) =>
    match kindOfWord w with
    | .error r => .error r
    | .ok k =>
      match splitAt? 0 rest with
      | none => .error .malformed
      | some (ds, _) =>
        if validDec ds then .ok (k, decValue ds, w.length + ds.length + 2) else .error .malformed

/-- Read one whole raw object: its kind and content. -/
def parseRaw (x : ByteArray) : Option (Kind × ByteArray) :=
  match parseHeaderL x.data.toList with
  | .ok (k, n, h) => if h + n = x.size then some (k, x.extract h x.size) else none
  | .error _ => none

#guard rawOf .blob "hello\n".toUTF8 == "blob 6\x00hello\n".toUTF8
#guard parseRaw (rawOf .tree "xyz".toUTF8) == some (.tree, "xyz".toUTF8)
#guard parseRaw "tag 3\x00xyz".toUTF8 == none && parseRaw "blob 03\x00xyz".toUTF8 == none

/-! ## Trees and commits (the allow-list grammar) -/

/-- The first position `≥ i` holding byte `x`. -/
def findByte (b : ByteArray) (x : UInt8) (i : Nat) : Option Nat :=
  if h : i < b.size then if b[i] = x then some i else findByte b x (i + 1) else none
termination_by b.size - i

/-- A tree entry's mode: `false` for a file (100644, 100755, 120000), `true` for a tree (40000);
a gitlink (160000) is refused with `GITLINK`, any other mode with `MALFORMED`. -/
def modeOf (m : ByteArray) : Except ObjReason Bool :=
  if m = "100644".toUTF8 ∨ m = "100755".toUTF8 ∨ m = "120000".toUTF8 then .ok false
  else if m = "40000".toUTF8 then .ok true
  else if m = "160000".toUTF8 then .error .gitlink
  else .error .malformed

/-- A tree entry's name: not empty, no `/` (a NUL ends it), not `.` or `..`. -/
def validEntryName (n : ByteArray) : Bool :=
  0 < n.size && !n.data.contains 0x2f && n != ".".toUTF8 && n != "..".toUTF8

/-- Read a tree: entries `<mode> SP <name> NUL <32 bytes>`, in git's tree order (names compared
byte by byte, a tree's name as if it ended in `/`), strictly increasing, no name twice. The ids
of its entries. -/
def parseTree (c : ByteArray) : Except ObjReason (Array Oid) :=
  go (c.size + 1) 0 none ∅ #[]
where
  /-- The entries from position `p` on; `prev` is the previous entry's sort key, `seen` the names
  so far. -/
  go : Nat → Nat → Option ByteArray → Std.TreeSet ByteArray compareBytes → Array Oid →
      Except ObjReason (Array Oid)
    | 0, _, _, _, _ => .error .malformed
    | fuel + 1, p, prev, seen, acc =>
      if c.size ≤ p then .ok acc
      else
        match findByte c 0x20 p with
        | none => .error .malformed
        | some sp =>
          match modeOf (c.extract p sp) with
          | .error r => .error r
          | .ok isTree =>
            match findByte c 0 (sp + 1) with
            | none => .error .malformed
            | some z =>
              let name := c.extract (sp + 1) z
              let key := if isTree then name.push 0x2f else name
              if c.size < z + 33 || !validEntryName name || seen.contains name ||
                  prev.any (fun k => compareBytes k key != .lt) then .error .malformed
              else
                match Digest.ofBytes? (c.extract (z + 1) (z + 33)) with
                | none => .error .malformed
                | some id => go fuel (z + 33) (some key) (seen.insert name) (acc.push id)

/-- A lower-case hex digit's value. -/
def hexNibble? (c : UInt8) : Option UInt8 :=
  if 48 ≤ c ∧ c ≤ 57 then some (c - 48) else if 97 ≤ c ∧ c ≤ 102 then some (c - 87) else none

/-- 64 lower-case hex digits as an id. -/
def hexOid? (b : ByteArray) : Option Oid :=
  if b.size = 64 then
    ((List.range 32).mapM fun i => do
        let hi ← hexNibble? b[2 * i]!
        let lo ← hexNibble? b[2 * i + 1]!
        pure (hi * 16 + lo)).bind fun l => Digest.ofBytes? ⟨l.toArray⟩
  else none

/-- `b` starts with `pre`. -/
def startsWith (b pre : ByteArray) : Bool := pre.size ≤ b.size && b.extract 0 pre.size == pre

/-- The line from position `p`: its bytes without the newline, and the position after it. -/
def lineAt (c : ByteArray) (p : Nat) : Option (ByteArray × Nat) :=
  (findByte c 0x0a p).map fun nl => (c.extract p nl, nl + 1)

/-- A header line `<pre><64 hex>`: the id. -/
def hexLine? (pre l : ByteArray) : Option Oid :=
  if l.size = pre.size + 64 ∧ startsWith l pre then hexOid? (l.extract pre.size l.size) else none

/-- The `parent` lines from position `p`, then the position of the first other line. -/
def parentsFrom (c : ByteArray) : Nat → Nat → List Oid → Option (List Oid × Nat)
  | 0, _, _ => none
  | fuel + 1, p, acc =>
    match lineAt c p with
    | none => none
    | some (l, q) =>
      match hexLine? "parent ".toUTF8 l with
      | some o => parentsFrom c fuel q (o :: acc)
      | none => some (acc.reverse, p)

/-- From position `p`: an `author` line, a `committer` line, an optional `encoding` line, then a
blank line. -/
def identsFrom (c : ByteArray) (p : Nat) : Bool :=
  match lineAt c p with
  | some (a, p) =>
    startsWith a "author ".toUTF8 &&
    match lineAt c p with
    | some (cm, p) =>
      startsWith cm "committer ".toUTF8 &&
      match lineAt c p with
      | some (l, p) =>
        l.size == 0 ||
          (startsWith l "encoding ".toUTF8 &&
            match lineAt c p with
            | some (l, _) => l.size == 0
            | none => false)
      | none => false
    | none => false
  | none => false

/-- Read a commit's header: exactly `tree <64 hex>`, any number of `parent <64 hex>`, `author`,
`committer`, an optional `encoding`, then a blank line. Every other header (`gpgsig`,
`gpgsig-sha256`, `mergetag`, a continuation line, an unknown one) is refused with `HEADER`. The
tree and the parents. -/
def parseCommit (c : ByteArray) : Except ObjReason (Oid × List Oid) :=
  match lineAt c 0 with
  | none => .error .header
  | some (l, p) =>
    match hexLine? "tree ".toUTF8 l with
    | none => .error .header
    | some t =>
      match parentsFrom c (c.size + 1) p [] with
      | none => .error .header
      | some (ps, q) => if identsFrom c q then .ok (t, ps) else .error .header

/-- The grammar check of an object's content: blobs pass; trees and commits must read. -/
def checkContent : Kind → ByteArray → Except ObjReason Unit
  | .blob, _ => .ok ()
  | .tree, c => (parseTree c).map fun _ => ()
  | .commit, c => (parseCommit c).map fun _ => ()

/-! ## Objects and the stream -/

/-- An object of a push: its kind, content, raw form and id. -/
structure Obj where
  /-- Commit, tree or blob. -/
  kind : Kind
  /-- The content, after the header. -/
  content : ByteArray
  /-- The raw form, as it was in the stream. -/
  raw : ByteArray
  /-- The id: SHA-256 of `raw`. -/
  id : Oid
deriving DecidableEq

/-- The object passes the grammar of its kind. -/
def Obj.wellFormed (o : Obj) : Bool :=
  match checkContent o.kind o.content with
  | .ok _ => true
  | .error _ => false

/-- The ids an object references: a commit its tree and parents, a tree its entries. -/
def refsOf (o : Obj) : List Oid :=
  match o.kind with
  | .blob => []
  | .tree => match parseTree o.content with | .ok ids => ids.toList | .error _ => []
  | .commit => match parseCommit o.content with | .ok (t, ps) => t :: ps | .error _ => []

/-- A commit's parents (`[]` for a root commit, and for any other object). -/
def commitParents (o : Obj) : List Oid :=
  match o.kind with
  | .commit => match parseCommit o.content with | .ok (_, ps) => ps | .error _ => []
  | _ => []

/-- A root commit: a commit with no parent. -/
def Obj.isRoot (o : Obj) : Bool := o.kind == .commit && (commitParents o).isEmpty

/-- Read the object at position `p` of stream `s`: the object and the position after it. Its raw
bytes must be exactly `rawOf` of its kind and content (a canonical header), and its content must
pass the grammar of its kind. -/
def readObj (s : ByteArray) (p : Nat) : Except (ObjReason × Oid) (Obj × Nat) :=
  match parseHeaderL (s.extract p (p + 32)).data.toList with
  | .error r => .error (r, zeroOid)
  | .ok (k, n, h) =>
    let e := p + h + n
    if s.size < e then .error (.malformed, zeroOid)
    else
      let raw := s.extract p e
      let content := s.extract (p + h) e
      if raw ≠ rawOf k content then .error (.malformed, zeroOid)
      else
        let id := sha256 raw
        match checkContent k content with
        | .error r => .error (r, id)
        | .ok _ => .ok (⟨k, content, raw, id⟩, e)

/-- Cut the stream from position `p` into objects, after `acc`. -/
def objectsFrom (s : ByteArray) : Nat → Nat → Array Obj → Except (ObjReason × Oid) (Array Obj)
  | 0, _, _ => .error (.malformed, zeroOid)
  | fuel + 1, p, acc =>
    if s.size ≤ p then .ok acc
    else if maxObjects ≤ acc.size then .error (.limits, zeroOid)
    else
      match readObj s p with
      | .error e => .error e
      | .ok (o, e) => objectsFrom s fuel e (acc.push o)

/-- The first id that is not above the one before it. -/
def firstUnordered : List Oid → Oid
  | a :: b :: rest => if compare a b == .lt then firstUnordered (b :: rest) else b
  | _ => zeroOid

/-- Check a push's stream: cut it into raw objects (at most 512), recompute each id, check each
tree and commit, and check that the ids are strictly increasing. -/
def checkObjectsE (s : ByteArray) : Except (ObjReason × Oid) (Array Obj) :=
  match objectsFrom s (s.size + 1) 0 #[] with
  | .error e => .error e
  | .ok os =>
    if isStrictlySortedList (os.map (·.id)).toList then .ok os
    else .error (.order, firstUnordered (os.map (·.id)).toList)

/-- `checkObjectsE`, without the reason. -/
def checkObjects (s : ByteArray) : Option (Array Obj) :=
  match checkObjectsE s with
  | .ok os => some os
  | .error _ => none

/-! ## The push body (field 212) -/

/-- One ref update of a push. -/
structure Update where
  /-- The ref name (`refs/heads/*` or `refs/tags/*`). -/
  name : String
  /-- The value the pusher saw and replaces (G-M2); `none`: a create. -/
  old : Option Oid
  /-- The new value; `none`: a delete. -/
  new : Option Oid
  /-- The pusher's force flag (not checked: `zrdtd` does not check ancestry). -/
  forced : Bool
deriving DecidableEq, Repr

/-- The push body: `"zgit1" ‖ flags u8 ‖ repo (u8 len ‖ name) ‖ updates (u8 count ‖ update…)
‖ u16 nO ‖ nO oids ‖ u16 nC ‖ nC seats`. -/
structure Body where
  /-- Bit 0 of the flags: a deliberate share. -/
  share : Bool
  /-- The repository name. -/
  repo : String
  /-- The ref updates, strictly increasing by name. -/
  updates : Array Update
  /-- The ids of the objects the push carries, strictly increasing. -/
  oids : Array Oid
  /-- A share's covers: the seats it gives objects they were not entitled to. -/
  covers : Array Serve.Seat
deriving DecidableEq

/-- An ASCII letter or digit. -/
def isAlnum (c : UInt8) : Bool := (48 ≤ c && c ≤ 57) || (65 ≤ c && c ≤ 90) || (97 ≤ c && c ≤ 122)

/-- A repository name: 1 to 64 bytes of `[A-Za-z0-9._-]`, the first one a letter or digit. -/
def validRepoName (s : String) : Bool :=
  let b := s.toUTF8
  0 < b.size && b.size ≤ maxRepoName && isAlnum b[0]! &&
    b.data.all fun c => isAlnum c || c == 0x2e || c == 0x5f || c == 0x2d

/-- `pat` occurs in `b`. -/
def containsSub (b pat : ByteArray) : Bool :=
  (List.range (b.size + 1 - pat.size)).any fun i => b.extract i (i + pat.size) == pat

/-- `b` ends with `suf`. -/
def endsWith (b suf : ByteArray) : Bool :=
  suf.size ≤ b.size && b.extract (b.size - suf.size) b.size == suf

/-- A ref name (GIT_PLAN §2.3, with BUILD_M1 §B.3's `refs/heads/*` and `refs/tags/*` only):
at most 250 bytes; under `refs/heads/` or `refs/tags/`; no byte up to space, no DEL, none of
`~^:?*[\`; no `..`, `@{`, `//`, `/.` (a component starting with a dot), `.lock/`; no `.zrdt-`
(reserved for the helper's listing); not ending in `/`, `.` or `.lock`. -/
def validRefName (s : String) : Bool :=
  let b := s.toUTF8
  b.size ≤ maxRefName &&
    (startsWith b "refs/heads/".toUTF8 || startsWith b "refs/tags/".toUTF8) &&
    b.data.all (fun c => 0x20 < c && c != 0x7f && !"~^:?*[\\".toUTF8.data.contains c) &&
    !["..", "@{", "//", "/.", ".lock/", ".zrdt-"].any (fun p => containsSub b p.toUTF8) &&
    !["/", ".", ".lock"].any (fun p => endsWith b p.toUTF8)

#guard validRefName "refs/heads/main" && validRefName "refs/tags/v1.0" &&
  validRefName "refs/heads/feature/x-1"
#guard !validRefName "refs/heads/" && !validRefName "refs/notes/x" && !validRefName "HEAD" &&
  !validRefName "refs/heads/a..b" && !validRefName "refs/heads/.x" && !validRefName "refs/heads/x.lock" &&
  !validRefName "refs/heads/x y" && !validRefName "refs/heads/main.zrdt-0123" &&
  !validRefName "refs/heads/a//b" && !validRefName "refs/heads/x." && !validRefName "refs/heads/@{1}"
#guard validRepoName "demo" && validRepoName "my-repo.git" && !validRepoName "-x" &&
  !validRepoName "" && !validRepoName "a/b"

/-- An update of a push body: a valid name of 1 to 250 bytes, and a value on at least one side. -/
def Update.wellFormed (u : Update) : Bool :=
  0 < u.name.toUTF8.size && u.name.toUTF8.size ≤ maxRefName && validRefName u.name &&
    (u.old.isSome || u.new.isSome)

/-- Each name below the next (byte order), so no name repeats. -/
def namesIncreasing : List Update → Bool
  | a :: b :: rest => compareBytes a.name.toUTF8 b.name.toUTF8 == .lt && namesIncreasing (b :: rest)
  | _ => true

/-- The order of seats: by ACI, then by tag. -/
def seatLt (a b : Serve.Seat) : Bool :=
  compare a.aci b.aci == .lt || (a.aci == b.aci && compareBytes ⟨a.tag⟩ ⟨b.tag⟩ == .lt)

/-- Each seat below the next. -/
def seatsIncreasing : List Serve.Seat → Bool
  | a :: b :: rest => seatLt a b && seatsIncreasing (b :: rest)
  | _ => true

/-- A body `writeBody` writes and `parseBody` reads: a valid repository name; at most 16 valid
updates, strictly increasing by name; at most 512 ids, strictly increasing; at most 256 covers of
16-byte tags, strictly increasing, and none unless the push is a share. -/
def Body.wellFormed (b : Body) : Bool :=
  b.repo.toUTF8.size ≤ maxRepoName && validRepoName b.repo &&
    b.updates.size ≤ maxUpdates && b.updates.all Update.wellFormed &&
    namesIncreasing b.updates.toList &&
    b.oids.size ≤ maxObjects && isStrictlySortedList b.oids.toList &&
    b.covers.size ≤ Serve.maxAudience && b.covers.all (·.tag.size == 16) &&
    seatsIncreasing b.covers.toList && (b.share || b.covers.isEmpty)

/-! ### Writing and reading the body (on lists of bytes) -/

/-- `"zgit1"`. -/
def bodyTagL : List UInt8 := [0x7a, 0x67, 0x69, 0x74, 0x31]

#guard bodyTagL.toArray == "zgit1".toUTF8.data

/-- A `u16`, big-endian. -/
def u16L (n : Nat) : List UInt8 := [(n / 256).toUInt8, n.toUInt8]

/-- An id's 32 bytes. -/
def oidL (o : Oid) : List UInt8 := o.bytes.data.toList

/-- `optoid`: 0, or 1 and the id. -/
def optOidL : Option Oid → List UInt8
  | none => [0]
  | some o => 1 :: oidL o

/-- A short name: its length as one byte, then its UTF-8 bytes. -/
def nameL (s : String) : List UInt8 := s.toUTF8.size.toUInt8 :: s.toUTF8.data.toList

/-- A flag byte. -/
def flagL (b : Bool) : UInt8 := if b then 1 else 0

/-- An `update`: name ‖ old ‖ new ‖ forced. -/
def updateL (u : Update) : List UInt8 :=
  nameL u.name ++ (optOidL u.old ++ (optOidL u.new ++ [flagL u.forced]))

/-- A `seat`: ACI ‖ tag. -/
def seatL (s : Serve.Seat) : List UInt8 := s.aci.bytes.data.toList ++ s.tag.toList

/-- The body's bytes, as a list. -/
def writeBodyL (b : Body) : List UInt8 :=
  bodyTagL ++ flagL b.share :: (nameL b.repo ++ b.updates.size.toUInt8 ::
    (b.updates.toList.flatMap updateL ++ (u16L b.oids.size ++ (b.oids.toList.flatMap oidL ++
      (u16L b.covers.size ++ b.covers.toList.flatMap seatL)))))

/-- The body's bytes (field 212). -/
def writeBody (b : Body) : ByteArray := ⟨(writeBodyL b).toArray⟩

/-- A reader of a list of bytes: a value and the rest, or `none`. -/
abbrev LP (α : Type) := List UInt8 → Option (α × List UInt8)

/-- One byte. -/
def lpU8 : LP UInt8
  | x :: xs => some (x, xs)
  | [] => none

/-- `n` bytes. -/
def lpTake (n : Nat) : LP (List UInt8) := fun l =>
  if n ≤ l.length then some (l.take n, l.drop n) else none

/-- A `u16`. -/
def lpU16 : LP Nat
  | hi :: lo :: rest => some (hi.toNat * 256 + lo.toNat, rest)
  | _ => none

/-- An id. -/
def lpOid : LP Oid := fun l =>
  match lpTake 32 l with
  | some (xs, rest) => (Digest.ofBytes? ⟨xs.toArray⟩).map (·, rest)
  | none => none

/-- `optoid`. -/
def lpOptOid : LP (Option Oid)
  | 0 :: rest => some (none, rest)
  | 1 :: rest => (lpOid rest).map fun (o, r) => (some o, r)
  | _ => none

/-- A flag. -/
def lpFlag : LP Bool
  | 0 :: rest => some (false, rest)
  | 1 :: rest => some (true, rest)
  | _ => none

/-- A short name (UTF-8). -/
def lpName : LP String
  | n :: rest =>
    match lpTake n.toNat rest with
    | some (xs, r) => (String.fromUTF8? ⟨xs.toArray⟩).map (·, r)
    | none => none
  | [] => none

/-- An `update`. -/
def lpUpdate : LP Update := fun l =>
  match lpName l with
  | none => none
  | some (name, l) =>
    match lpOptOid l with
    | none => none
    | some (old, l) =>
      match lpOptOid l with
      | none => none
      | some (new, l) =>
        match lpFlag l with
        | none => none
        | some (forced, l) => some (⟨name, old, new, forced⟩, l)

/-- A `seat`. -/
def lpSeat : LP Serve.Seat := fun l =>
  match lpTake 16 l with
  | none => none
  | some (a, l) =>
    match lpTake 16 l with
    | none => none
    | some (t, l) => (Aci.ofBytes? ⟨a.toArray⟩).map fun aci => (⟨aci, t.toArray⟩, l)

/-- `n` items. -/
def lpMany {α : Type} (p : LP α) : Nat → LP (List α)
  | 0 => fun l => some ([], l)
  | n + 1 => fun l =>
    match p l with
    | none => none
    | some (x, l) =>
      match lpMany p n l with
      | none => none
      | some (xs, l) => some (x :: xs, l)

/-- Read a body's fields (no check of the limits or the order). -/
def parseBodyL (l : List UInt8) : Option Body :=
  match lpTake 5 l with
  | none => none
  | some (t, l) =>
    if t ≠ bodyTagL then none else
    match lpFlag l with
    | none => none
    | some (share, l) =>
      match lpName l with
      | none => none
      | some (repo, l) =>
        match lpU8 l with
        | none => none
        | some (nU, l) =>
          match lpMany lpUpdate nU.toNat l with
          | none => none
          | some (us, l) =>
            match lpU16 l with
            | none => none
            | some (nO, l) =>
              match lpMany lpOid nO l with
              | none => none
              | some (os, l) =>
                match lpU16 l with
                | none => none
                | some (nC, l) =>
                  match lpMany lpSeat nC l with
                  | none => none
                  | some (cs, l) =>
                    if l ≠ [] then none else some ⟨share, repo, us.toArray, os.toArray, cs.toArray⟩

/-- Read a push body: only a well-formed body that `writeBody` writes back to exactly these bytes,
so the meaning of a push is unique (`writeBody_parseBody`, `parseBody_writeBody`). -/
def parseBody (x : ByteArray) : Option Body :=
  match parseBodyL x.data.toList with
  | some b => if b.wellFormed ∧ writeBody b = x then some b else none
  | none => none

/-! ## The table (BUILD_M1 §B.7) -/

/-- A git record of the channel, read from its held opening. -/
structure Entry where
  /-- The record's digest. -/
  digest : Digest
  /-- Its author. -/
  author : Aci
  /-- Its audience (field 201), parsed. -/
  seats : Array Serve.Seat
  /-- Its push body. -/
  body : Body
  /-- The record's links. -/
  links : Array Digest

/-- The pusher's table: the channel store's git records with a held opening, and the store. -/
structure Table where
  /-- The entries, sorted by digest. -/
  entries : List Entry
  /-- A closed store whose every stored record has a held opening that matches it. -/
  complete : Bool
  /-- The channel store's records. -/
  map : RecMap

/-- The stored digests reachable from an entry's links: the records it saw. -/
def Table.reach (t : Table) (f : Entry) : DigestSet :=
  walk (fun r => r.links.toList) t.map ∅ f.links.toList

/-- The first held opening for digest `d` that matches record `r`. -/
def heldFor (hs : Array (Digest × ByteArray)) (d : Digest) (r : Rec) : Option ByteArray :=
  (hs.find? fun (d', o) => d' == d && openingMatches r.group r.author r.commit o).map (·.2)

/-- The entry of record `r` (digest `d`) with opening `o`: a canonical app message of
`git-sha256` / `repos` with a valid audience and a push body that reads. -/
def entryOf (d : Digest) (r : Rec) (o : ByteArray) : Option Entry :=
  match appOf o with
  | none => none
  | some h =>
    if h.app = appGit ∧ h.channel = channelGit then
      match Serve.parseAudience h.audience, parseBody h.body with
      | some seats, some b => some ⟨d, r.author, seats, b, r.links⟩
      | _, _ => none
    else none

/-- The table of a store's records `m` with held openings `hs`; `closed`: the store is closed. -/
def tableOfMap (m : RecMap) (closed : Bool) (hs : Array (Digest × ByteArray)) : Table :=
  { entries := m.toList.filterMap fun (d, r) => (heldFor hs d r).bind (entryOf d r)
    complete := closed && m.toList.all fun (d, r) => (heldFor hs d r).isSome
    map := m }

/-- The table of a channel. A relative store (a newcomer's, or a member's whose key changed) is
never complete, even with no boundary digest left. -/
def tableOf (ch : Proto.Chat) (hs : Array (Digest × ByteArray)) : Table :=
  tableOfMap ch.store.raw.map (!ch.store.isRelative) hs

/-- The table of a checked store (the statement form). -/
def tableOfStore (c : CheckedStore) (hs : Array (Digest × ByteArray)) : Table :=
  tableOfMap c.raw.map true hs

/-- Every stored record of `c` has a held opening that matches it. -/
def Complete (c : CheckedStore) (hs : Array (Digest × ByteArray)) : Prop :=
  ∀ d r, c.raw.map[d]? = some r → ∃ o, (d, o) ∈ hs ∧ openingMatches r.group r.author r.commit o = true

/-- Entry `e`'s audience seats `s`: the same ACI and tag, and the tag is not zero. -/
def seated (e : Entry) (s : Serve.Seat) : Bool :=
  s.tag != Serve.zeroTag && e.seats.any fun x => x.aci == s.aci && x.tag == s.tag

/-- Seat `s` is entitled to id `o`: some entry lists `o` and seats `s`. -/
def entitled (t : Table) (s : Serve.Seat) (o : Oid) : Bool :=
  t.entries.any fun e => seated e s && e.body.oids.contains o

/-- Some entry lists `o`. -/
def listed (t : Table) (o : Oid) : Bool := t.entries.any fun e => e.body.oids.contains o

/-- Some entry seats `s`'s ACI under another non-zero tag: its key changed. -/
def keyChanged (t : Table) (s : Serve.Seat) : Bool :=
  t.entries.any fun e => e.seats.any fun x => x.aci == s.aci && x.tag != s.tag && x.tag != Serve.zeroTag

/-- Entry `e` assigns value `v` to ref `n` of repository `repo`. -/
def assigns (e : Entry) (repo n : String) (v : Option Oid) : Bool :=
  e.body.repo == repo && e.body.updates.any fun u => u.name == n && u.new == v

/-! ## `GIT_PREPARE`: the pusher's checks -/

/-- A `GIT_PREPARE` request. -/
structure PrepareReq where
  /-- The Signal group. -/
  sg : GroupId
  /-- The channel store's key. -/
  channelKey : String
  /-- The pusher. -/
  author : Aci
  /-- The piece store's nonce. -/
  nonce : Nonce
  /-- log₂ of the piece size (20, or 10 in tests). -/
  exp : Nat
  /-- The audience, as `AUDIENCE` returned it. -/
  audience : ByteArray
  /-- A deliberate share. -/
  share : Bool
  /-- The covers the dialog showed (a share). -/
  expect : Array Serve.Seat
  /-- The repository. -/
  repo : String
  /-- The ref updates. -/
  updates : Array Update
  /-- Every opening the host holds for the channel. -/
  helds : Array (Digest × ByteArray)
  /-- The piece pointers (field 216). -/
  pointers : ByteArray
  /-- The raw objects, ids strictly increasing. -/
  stream : ByteArray

/-- What `GIT_PREPARE` returns, and what it decided. -/
structure Prepared where
  /-- The committed bytes of the push record (an app message). -/
  message : ByteArray
  /-- The piece digests (empty when the stream is empty). -/
  ordered : Array Digest
  /-- A share's covers. -/
  covers : Array Serve.Seat
  /-- The objects the push carries. -/
  objects : Array Obj
  /-- The push body. -/
  body : Body

/-- Why a push is refused: the reason byte of `PUSH_REFUSED`. -/
inductive PushReason
  /-- 1: a root commit from an incomplete table (G-F1). -/
  | root
  /-- 2: an object some entry lists (G-M6). -/
  | oldObject
  /-- 3: a checked seat is not entitled to what the push builds on, or not seated where the
  replaced value was assigned (G-M1). -/
  | gate
  /-- 4: a share that is not exact (G-M7). -/
  | badShare
  /-- 5: a covered seat's key changed. -/
  | keyChanged
  /-- 6: the covers are not those the dialog showed. -/
  | coversChanged
deriving DecidableEq, Repr

/-- The reason byte. -/
def PushReason.byte : PushReason → UInt8
  | .root => 1 | .oldObject => 2 | .gate => 3 | .badShare => 4 | .keyChanged => 5
  | .coversChanged => 6

/-- A refusal of `GIT_PREPARE`. -/
inductive Refusal
  /-- `BAD_APP` with a reason. -/
  | badApp (r : BadApp)
  /-- `BAD_OBJECTS`: the reason and the object (zero when there is none). -/
  | badObjects (r : ObjReason) (o : Oid)
  /-- `PUSH_REFUSED`: the reason, the seats with their marks (0 new, 1 key changed, 2 covered),
  the ref names and the ids concerned. -/
  | pushRefused (r : PushReason) (seats : Array (Serve.Seat × UInt8)) (names : Array String)
      (oids : Array Oid)

/-- The audience's seats that the gate checks: a non-zero tag, and not the pusher's own ACI. -/
def checkedSeats (req : PrepareReq) : Array Serve.Seat :=
  match Serve.parseAudience req.audience with
  | some a => a.filter fun s => s.tag != Serve.zeroTag && s.aci != req.author
  | none => #[]

/-- The ids the carried objects reference, and every update's old and new value, without the
carried ids: what the push builds on. -/
def refsOutOf (os : Array Obj) (us : Array Update) : List Oid :=
  let carried : DigestSet := os.foldl (fun acc o => acc.insert o.id) ∅
  let all := os.toList.flatMap refsOf ++ us.toList.flatMap fun u => u.old.toList ++ u.new.toList
  (all.foldl (fun acc x => if carried.contains x then acc else acc.insert x) (∅ : DigestSet)).toList

/-- What a prepared push builds on. -/
def refsOut (out : Prepared) : List Oid := refsOutOf out.objects out.body.updates

/-- The carried commits' ids, in stream order. -/
def commitIds (out : Prepared) : List Oid :=
  (out.objects.toList.filter (·.kind == .commit)).map (·.id)

/-- The carried commits' parents. -/
def parentIds (out : Prepared) : List Oid := out.objects.toList.flatMap commitParents

/-- The updates' new values, increasing, without repeats. -/
def newValues (req : PrepareReq) : List Oid :=
  ((req.updates.toList.filterMap (·.new)).foldl (fun acc x => acc.insert x) (∅ : DigestSet)).toList

/-- A share's covers: the checked seats that are not entitled to some carried id that an entry
lists. -/
def coversOf (t : Table) (req : PrepareReq) (out : Prepared) : Array Serve.Seat :=
  (checkedSeats req).filter fun s =>
    out.objects.any fun o => listed t o.id && !entitled t s o.id

/-- Updates sorted by name (the body's order). -/
def sortUpdates (us : Array Update) : Array Update :=
  (us.toList.mergeSort fun a b => compareBytes a.name.toUTF8 b.name.toUTF8 != .gt).toArray

/-- The name rule for seat `s` and update `u`: if `u` replaces a value, `s` is seated in an
entry that assigned that value to that name. -/
def nameRuleOk (t : Table) (req : PrepareReq) (s : Serve.Seat) (u : Update) : Bool :=
  match u.old with
  | none => true
  | some v => t.entries.any fun e => seated e s && assigns e req.repo u.name (some v)

/-- The gate for seat `s`: entitled to everything the push builds on, and the name rule for every
update. -/
def gateOk (t : Table) (req : PrepareReq) (refs : List Oid) (s : Serve.Seat) : Bool :=
  refs.all (entitled t s) && req.updates.all (nameRuleOk t req s)

/-- The context the receivers' `PIECES_BIND` will give the push's pieces: channel `ch`, the
pusher, the store nonce, piece size `2^k` and the audience. -/
def streamCtx (ch : GroupId) (req : PrepareReq) : PieceCtx :=
  { announcement := Digest.zero, channel := ch, author := req.author
    header := { audience := req.audience, app := appGit, channel := channelGit, body := .empty }
    seats := #[], desc := ⟨req.nonce, req.stream.size, req.exp, #[], .empty⟩ }

/-- The digests of the stream's pieces, in index order. -/
def orderedOf (c : PieceCtx) (s : ByteArray) : Array Digest :=
  (Array.range (pieceCount c.desc.exp s.size)).map fun i =>
    hashRecord (pieceRecord c i (slice c.desc.exp s i))

/-- The push record's message: an app message of `git-sha256` / `repos` with the body, and, when
the stream is not empty, the descriptor (empty app manifest) and the pointers (if any); and the
piece digests. -/
def messageOf (req : PrepareReq) (body : Body) : AppHeader × Array Digest :=
  let L := req.stream.size
  let ordered :=
    if L = 0 then #[] else orderedOf (streamCtx (channelId req.sg appGit channelGit) req) req.stream
  let desc : Descriptor := ⟨req.nonce, L, req.exp, ordered, .empty⟩
  ({ audience := req.audience, app := appGit, channel := channelGit, body := writeBody body
     descriptor := if L = 0 then none else some desc.write
     pointers := if L = 0 ∨ req.pointers.size = 0 then none else some req.pointers }, ordered)

/-- The limits of the request (`BAD_APP` 6): an audience `ACCEPT` takes, piece size 2^20 or 2^10,
a stream of at most 64 pieces, pointers within 16 KiB and only with a stream. -/
def limitsOk (req : PrepareReq) : Bool :=
  (Serve.parseAudience req.audience).isSome && pieceExpOk req.exp &&
    req.stream.size ≤ maxPieces * 2 ^ req.exp && req.pointers.size ≤ maxPointers &&
    (0 < req.stream.size || req.pointers.size == 0)

/-- The update list's reason to refuse, if any: more than 16 (`LIMITS`), a bad repository or ref
name (`NAME`), a repeated name, an update with neither value, or a delete in a share (`LIST`). -/
def updatesError (req : PrepareReq) (us : Array Update) : Option ObjReason :=
  if maxUpdates < us.size then some .limits
  else if !validRepoName req.repo || !us.all (fun u => validRefName u.name) then some .name
  else if !us.all Update.wellFormed || !namesIncreasing us.toList ||
      (req.share && us.any fun u => u.new.isNone) then some .list
  else none

/-- The mark of a failing seat: 1 if its key changed, 0 (new) otherwise. -/
def markOf (t : Table) (s : Serve.Seat) : UInt8 := if keyChanged t s then 1 else 0

/-- The result of a push that passed its checks. -/
def finish (req : PrepareReq) (os : Array Obj) (us : Array Update) (covers : Array Serve.Seat) :
    Except Refusal Prepared :=
  let body : Body := ⟨req.share, req.repo, us, os.map (·.id), covers⟩
  let hm := messageOf req body
  if body.wellFormed && hm.1.wellFormed then .ok ⟨appMessage hm.1, hm.2, covers, os, body⟩
  else .error (.badApp .limits)

/-- The checks of a non-share push, in order: the root rule, freshness, the gate. -/
def checkPlain (t : Table) (req : PrepareReq) (os : Array Obj) (us : Array Update) :
    Except Refusal Prepared :=
  let refs := refsOutOf os us
  if !(t.complete || os.all fun o => !o.isRoot) then
    .error (.pushRefused .root #[] #[] ((os.filter (·.isRoot)).map (·.id)))
  else if !os.all (fun o => !listed t o.id) then
    .error (.pushRefused .oldObject #[] #[] ((os.filter fun o => listed t o.id).map (·.id)))
  else
    let failing := (checkedSeats req).filter fun s => !gateOk t req refs s
    if !failing.isEmpty then
      .error (.pushRefused .gate (failing.map fun s => (s, markOf t s))
        ((req.updates.filter fun u => failing.any fun s => !nameRuleOk t req s u).map (·.name))
        ((refs.filter fun x => failing.any fun s => !entitled t s x).toArray))
    else finish req os us #[]

/-- The checks of a share, in order: exactness (`BAD_SHARE`), keys (`KEY_CHANGED`), the dialog's
covers (`COVERS_CHANGED`). -/
def checkShare (t : Table) (req : PrepareReq) (os : Array Obj) (us : Array Update) :
    Except Refusal Prepared :=
  let pre : Prepared := ⟨.empty, #[], #[], os, ⟨true, req.repo, us, os.map (·.id), #[]⟩⟩
  let refs := refsOut pre
  let parents := parentIds pre
  if !(commitIds pre == newValues req && refs.all (parents.contains ·) &&
      req.updates.all fun u => u.old.all (some · == u.new)) then
    .error (.pushRefused .badShare #[]
      ((req.updates.filter fun u => !u.old.all (some · == u.new)).map (·.name))
      (((refs.filter fun x => !parents.contains x) ++ (commitIds pre).filter (· ∉ newValues req) ++
        (newValues req).filter (· ∉ commitIds pre)).foldl (fun acc x => acc.insert x)
          (∅ : DigestSet)).toList.toArray)
  else
    let covers := coversOf t req pre
    if covers.any (keyChanged t) then
      .error (.pushRefused .keyChanged ((covers.filter (keyChanged t)).map (·, 1)) #[] #[])
    else if covers != req.expect then
      .error (.pushRefused .coversChanged (covers.map (·, 2)) #[] #[])
    else finish req os us covers

/-- `GIT_PREPARE` once the channel and openings are checked: the limits, the objects, the updates,
then the checks of a plain push or of a share, and the message. Pure: the host commits and accepts
the message itself. -/
def prepare (t : Table) (req : PrepareReq) : Except Refusal Prepared :=
  if !limitsOk req then .error (.badApp .limits)
  else
    match checkObjectsE req.stream with
    | .error (r, o) => .error (.badObjects r o)
    | .ok os =>
      let us := sortUpdates req.updates
      match updatesError req us with
      | some r => .error (.badObjects r zeroOid)
      | none => if req.share then checkShare t req os us else checkPlain t req os us

/-! ## `GIT_VIEW`: the push log and the register -/

/-- One line of the push log. -/
structure LogEntry where
  /-- The push record's digest. -/
  digest : Digest
  /-- Its author. -/
  author : Aci
  /-- A share. -/
  share : Bool
  /-- The update. -/
  update : Update
deriving DecidableEq

/-- What `GIT_VIEW` returns for one repository. -/
structure View where
  /-- Every update of every push of the repository. -/
  log : List LogEntry
  /-- The live assignments (name, record, value). -/
  refs : List (String × Digest × Option Oid)
deriving DecidableEq

/-- Log order: by digest, then by name. -/
def logLe (a b : LogEntry) : Bool :=
  compare a.digest b.digest == .lt ||
    (a.digest == b.digest && compareBytes a.update.name.toUTF8 b.update.name.toUTF8 != .gt)

/-- Register order: by name, then by digest. -/
def refLe (a b : String × Digest × Option Oid) : Bool :=
  compareBytes a.1.toUTF8 b.1.toUTF8 == .lt || (a.1 == b.1 && compare a.2.1 b.2.1 != .gt)

/-- An assignment `(n, d, v)` is superseded when an entry that saw record `d` replaced `v` in
`n`. -/
def superseded (t : Table) (repo n : String) (d : Digest) (v : Option Oid) : Bool :=
  t.entries.any fun f =>
    f.body.updates.any (fun u => f.body.repo == repo && u.name == n && u.old == v) &&
      (t.reach f).contains d

/-- The view of repository `repo`: the log (every update of every entry of the repository) and
the live assignments (those no entry that saw them replaced). -/
def gitView (t : Table) (repo : String) : View :=
  let es := t.entries.filter (·.body.repo == repo)
  let log := es.flatMap fun e =>
    e.body.updates.toList.map fun u => (⟨e.digest, e.author, e.body.share, u⟩ : LogEntry)
  let assigned := es.flatMap fun e => e.body.updates.toList.map fun u => (u.name, e.digest, u.new)
  { log := log.mergeSort logLe
    refs := (assigned.filter fun (n, d, v) => !superseded t repo n d v).mergeSort refLe }

/-! ## The ops -/

/-- A git request. -/
inductive Request
  /-- `GIT_PREPARE`. -/
  | prepare (p : PrepareReq)
  /-- `GIT_OBJECTS`: a piece key and the stream. -/
  | objects (key : String) (stream : ByteArray)
  /-- `GIT_VIEW`: Signal group, channel key, repository, held openings. -/
  | view (sg : GroupId) (channelKey : String) (repo : String) (helds : Array (Digest × ByteArray))

/-- A git reply. -/
inductive Reply
  /-- `GIT_PREPARE` → `OK`. -/
  | prepared (out : Prepared)
  /-- `GIT_PREPARE` refused (`BAD_APP`, `BAD_OBJECTS`, `PUSH_REFUSED`). -/
  | refused (r : Refusal)
  /-- `GIT_OBJECTS` → `OK`. -/
  | objects (os : Array Obj)
  /-- `GIT_VIEW` → `OK`. -/
  | view (v : View)
  /-- `BAD_PIECE` with the first bad index. -/
  | badPiece (i : Nat)
  /-- `OPENINGS_MISSING`. -/
  | openingsMissing (ds : Array Digest)
  /-- A status with an empty body (`NO_CHAT`, `BAD_OPENING`). -/
  | code (c : Proto.Code)

namespace Write
open Proto.Write

/-- `optoid`. -/
def optOid (o : Option Oid) : ByteArray := ⟨(optOidL o).toArray⟩

/-- `refname`. -/
def refname (s : String) : ByteArray := ⟨(nameL s).toArray⟩

/-- `update`. -/
def update (u : Update) : ByteArray := ⟨(updateL u).toArray⟩

/-- `updates`: a `u8` count, then each update. -/
def updates (us : Array Update) : ByteArray :=
  us.foldl (fun acc u => acc ++ update u) (u8 us.size.toUInt8)

/-- `seat`. -/
def seat (s : Serve.Seat) : ByteArray := s.aci.bytes ++ ⟨s.tag⟩

/-- `seats`: a `u32` count, then each seat. -/
def seats (ss : Array Serve.Seat) : ByteArray :=
  ss.foldl (fun acc s => acc ++ seat s) (u32be ss.size)

/-- `helds`. -/
def helds (hs : Array (Digest × ByteArray)) : ByteArray :=
  hs.foldl (fun acc (d, o) => acc ++ d.bytes ++ bytes o) (u32be hs.size)

end Write

open Proto.Write in
/-- The request's payload (op byte first). -/
def Request.write : Request → ByteArray
  | .prepare p =>
    u8 0x28 ++ p.sg.bytes ++ str p.channelKey ++ p.author.bytes ++ p.nonce.bytes ++
      u8 p.exp.toUInt8 ++ bytes p.audience ++ flag p.share ++ Write.seats p.expect ++ str p.repo ++
      Write.updates p.updates ++ Write.helds p.helds ++ bytes p.pointers ++ bytes p.stream
  | .objects key st => u8 0x29 ++ str key ++ bytes st
  | .view sg ck repo hs => u8 0x2A ++ sg.bytes ++ str ck ++ str repo ++ Write.helds hs

/-- The objects of a `GIT_OBJECTS` reply: a count, then per object its kind, id, the offset of
its content in the stream, and the content's length. -/
def objectsBody (os : Array Obj) : ByteArray :=
  (os.foldl (fun (acc, off) o =>
      (acc ++ Proto.Write.u8 o.kind.byte ++ o.id.bytes ++
        u64be (off + (o.raw.size - o.content.size)) ++ u64be o.content.size,
       off + o.raw.size)) (u32be os.size, 0)).1

open Proto.Write in
/-- The reply's payload (status byte first). -/
def Reply.write : Reply → ByteArray
  | .prepared out =>
    Proto.Code.ok.write ++ bytes out.message ++ digests out.ordered ++ Write.seats out.covers
  | .refused (.badApp r) => Proto.Code.badApp.write ++ u8 r.byte
  | .refused (.badObjects r o) => Proto.Code.badObjects.write ++ u8 r.byte ++ o.bytes
  | .refused (.pushRefused r ss ns os) =>
    Proto.Code.pushRefused.write ++ u8 r.byte ++
      ss.foldl (fun acc (s, m) => acc ++ Write.seat s ++ u8 m) (u32be ss.size) ++
      ns.foldl (fun acc n => acc ++ Write.refname n) (u32be ns.size) ++ digests os
  | .objects os => Proto.Code.ok.write ++ objectsBody os
  | .view v =>
    Proto.Code.ok.write ++
      v.log.foldl (fun acc x => acc ++ x.digest.bytes ++ x.author.bytes ++ flag x.share ++
        Write.update x.update) (u32be v.log.length) ++
      v.refs.foldl (fun acc (n, d, o) => acc ++ Write.refname n ++ d.bytes ++ Write.optOid o)
        (u32be v.refs.length)
  | .badPiece i => Proto.Code.badPiece.write ++ u32be i
  | .openingsMissing ds => Proto.Code.openingsMissing.write ++ digests ds
  | .code c => c.write

namespace Parser
open Proto.Parser

/-- An `optoid`. -/
def optOid : Proto.Parser (Option Oid) := Proto.Parser.opt digest

/-- A `refname`: 1 to 250 bytes of UTF-8. -/
def refname : Proto.Parser String := do
  let n ← u8
  if n.toNat = 0 ∨ maxRefName < n.toNat then failure
  match String.fromUTF8? (← take n.toNat) with
  | some s => pure s
  | none => failure

/-- An `update`. -/
def update : Proto.Parser Update := do
  let n ← refname
  let o ← optOid
  let v ← optOid
  let f ← flag
  pure ⟨n, o, v, f⟩

/-- A `seat`. -/
def seat : Proto.Parser Serve.Seat := do
  let a ← aci
  let t ← take 16
  pure ⟨a, t.data⟩

/-- `seats`: strictly increasing by (ACI, tag). -/
def seats : Proto.Parser (Array Serve.Seat) := do
  let ss ← many seat 32 (← u32)
  if seatsIncreasing ss.toList then pure ss else failure

/-- `updates`. An update takes at least 5 bytes. -/
def updates : Proto.Parser (Array Update) := do many update 5 (← u8).toNat

/-- `helds`. A held item takes at least 36 bytes. -/
def helds : Proto.Parser (Array (Digest × ByteArray)) := do many Proto.Parser.held 36 (← u32)

/-- `GIT_PREPARE`'s body. -/
def prepare : Proto.Parser PrepareReq := do
  let sg ← group
  let channelKey ← str
  let author ← aci
  let nonce ← Proto.Parser.nonce
  let exp ← u8
  let audience ← bytes
  let share ← flag
  let expect ← seats
  let repo ← str
  let updates ← updates
  let helds ← helds
  let pointers ← bytes
  let stream ← bytes
  pure
    { sg := sg, channelKey := channelKey, author := author, nonce := nonce, exp := exp.toNat
      audience := audience, share := share, expect := expect, repo := repo, updates := updates
      helds := helds, pointers := pointers, stream := stream }

end Parser

/-- The body parser of git op `op` (`0x28`-`0x2F`); `none`: not a git op. -/
def parse (op : UInt8) : Option (Proto.Parser Request) :=
  match op with
  | 0x28 => some (.prepare <$> Parser.prepare)
  | 0x29 => some (.objects <$> Proto.Parser.str <*> Proto.Parser.bytes)
  | 0x2A => some (.view <$> Proto.Parser.group <*> Proto.Parser.str <*> Proto.Parser.str <*>
      Parser.helds)
  | _ => none

/-- A held opening that does not match its stored record. -/
def badHeld (ch : Proto.Chat) (hs : Array (Digest × ByteArray)) : Bool :=
  hs.any fun (d, o) =>
    match ch.store.get d with
    | some r => !openingMatches r.group r.author r.commit o
    | none => false

/-- The stored records with a recorded audience but no held opening, sorted. -/
def missingOpenings (ch : Proto.Chat) (hs : Array (Digest × ByteArray)) : Array Digest :=
  (ch.audiences.toList.filterMap fun (d, _) =>
    if ch.store.has d && !hs.any (·.1 == d) then some d else none).toArray

/-- The channel checks of `GIT_PREPARE` and `GIT_VIEW`: the store is the git channel of Signal
group `sg` (`BAD_APP` 1), every held opening matches (`BAD_OPENING`), and every record with a
recorded audience has a held opening (`OPENINGS_MISSING`). -/
def channelError (ch : Proto.Chat) (sg : GroupId) (hs : Array (Digest × ByteArray)) : Option Reply :=
  if ch.store.group ≠ channelId sg appGit channelGit then some (.refused (.badApp .notStored))
  else if badHeld ch hs then some (.code .badOpening)
  else
    let miss := missingOpenings ch hs
    if miss.isEmpty then none else some (.openingsMissing miss)

/-- The first piece of the stream that fails `pieceOk` (`N` if its length is not `L`). -/
def firstBadPiece (c : PieceCtx) (s : ByteArray) : Nat :=
  if s.size ≠ c.desc.len then c.count
  else ((List.range c.count).find? fun i => !pieceOk c i (slice c.desc.exp s i)).getD c.count

/-- Answer a git request. Read-only: the state does not change. -/
def run (s : State) : Request → Reply
  | .prepare p =>
    match s.chats[p.channelKey]? with
    | none => .code .noChat
    | some ch =>
      if ch.store.group ≠ channelId p.sg appGit channelGit then .refused (.badApp .notStored)
      else if !limitsOk p then .refused (.badApp .limits)
      else
        match channelError ch p.sg p.helds with
        | some r => r
        | none =>
          match prepare (tableOf ch p.helds) p with
          | .ok out => .prepared out
          | .error e => .refused e
  | .objects key st =>
    match s.ctxs[key]? with
    | none => .code .noChat
    | some ctx =>
      if ctx.header.app ≠ appGit then .refused (.badApp .wrongApp)
      else if !assembleOk ctx st then .badPiece (firstBadPiece ctx st)
      else
        match checkObjectsE st with
        | .error (r, o) => .refused (.badObjects r o)
        | .ok os =>
          match parseBody ctx.header.body with
          | none => .refused (.badObjects .list zeroOid)
          | some b =>
            if os.map (·.id) = b.oids then .objects os else .refused (.badObjects .list zeroOid)
  | .view sg ck repo hs =>
    match s.chats[ck]? with
    | none => .code .noChat
    | some ch =>
      match channelError ch sg hs with
      | some r => r
      | none => .view (gitView (tableOf ch hs) repo)

/-! ## Theorems (BUILD_M1 §C.3)

The statements of lane git that need no Mathlib, about the code above. `refs_agree` and
`force_visible`, which need `CheckedStore.agree`, are in `Crdt/Merkle/Api.lean` (Part 6c); they
rest on `gitView_congr` below. -/

/-! ### `checkObjects` -/

theorem readObj_spec {s : ByteArray} {p : Nat} {o : Obj} {e : Nat} (h : readObj s p = .ok (o, e)) :
    p ≤ e ∧ e ≤ s.size ∧ o.raw = s.extract p e ∧ o.raw = rawOf o.kind o.content ∧
      o.id = sha256 o.raw ∧ o.wellFormed = true := by
  unfold readObj at h
  split at h
  · cases h
  · rename_i k n hd _
    simp only at h
    split at h
    · cases h
    · rename_i hle
      split at h
      · cases h
      · rename_i hraw
        split at h
        · cases h
        · rename_i hc
          simp only [Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          refine ⟨by omega, by omega, rfl, Decidable.not_not.mp hraw, rfl, ?_⟩
          simp [Obj.wellFormed, hc]

theorem objectsFrom_sound {s : ByteArray} :
    ∀ {fuel p : Nat} {acc os : Array Obj}, objectsFrom s fuel p acc = .ok os → p ≤ s.size →
      s.extract 0 p = acc.foldl (fun a o => a ++ o.raw) .empty →
      (∀ o ∈ acc, o.raw = rawOf o.kind o.content ∧ o.id = sha256 o.raw ∧ o.wellFormed = true) →
      s = os.foldl (fun a o => a ++ o.raw) .empty ∧
        ∀ o ∈ os, o.raw = rawOf o.kind o.content ∧ o.id = sha256 o.raw ∧ o.wellFormed = true
  | 0, _, _, _, h, _, _, _ => by simp [objectsFrom] at h
  | fuel + 1, p, acc, os, h, hp, hs, ha => by
    unfold objectsFrom at h
    split at h
    · rename_i hle
      cases h
      have : p = s.size := by omega
      subst this
      exact ⟨by rw [← hs, ByteArray.extract_zero_size], ha⟩
    · split at h
      · cases h
      · split at h
        · cases h
        · rename_i o e hr
          obtain ⟨hpe, hes, hraw, h1, h2, h3⟩ := readObj_spec hr
          refine objectsFrom_sound h hes ?_ ?_
          · rw [ByteArray.extract_eq_extract_append_extract p (Nat.zero_le _) hpe, hs,
              Array.foldl_push, hraw]
          · intro x hx
            rcases Array.mem_push.mp hx with hx | rfl
            · exact ha x hx
            · exact ⟨h1, h2, h3⟩

/-- **The id check is sound** (BUILD_M1 §C.3): when `checkObjects` accepts a stream, the stream is
exactly its objects' raw forms one after another, each raw form is the canonical one of its kind
and content, each id is the SHA-256 of its raw form, each object passes its grammar, and the ids
are strictly increasing. -/
theorem checkObjects_sound {s : ByteArray} {os : Array Obj} (h : checkObjects s = some os) :
    s = os.foldl (fun acc o => acc ++ o.raw) .empty ∧
    (∀ o ∈ os, o.raw = rawOf o.kind o.content ∧ o.id.bytes = (sha256 o.raw).bytes ∧
      o.wellFormed = true) ∧
    ∀ i j (hi : i < os.size) (hj : j < os.size), i < j → compare os[i].id os[j].id = .lt := by
  unfold checkObjects at h
  split at h
  · rename_i os' hE
    cases h
    unfold checkObjectsE at hE
    split at hE
    · cases hE
    · rename_i os2 hfrom
      split at hE
      · rename_i hsort
        cases hE
        obtain ⟨h1, h2⟩ := objectsFrom_sound hfrom (Nat.zero_le _) (by simp) (by simp)
        refine ⟨h1, fun o ho => ⟨(h2 o ho).1, by rw [(h2 o ho).2.1], (h2 o ho).2.2⟩, ?_⟩
        intro i j hi hj hij
        have hp := (isStrictlySortedList_iff _).mp hsort
        rw [List.pairwise_iff_getElem] at hp
        have := hp i j (by simpa using hi) (by simpa using hj) hij
        simpa using this
      · cases hE
  · cases h

/-! ### `prepare` -/

/-- What `finish` returns. -/
theorem finish_ok {req : PrepareReq} {os : Array Obj} {us : Array Update} {cv : Array Serve.Seat}
    {out : Prepared} (h : finish req os us cv = .ok out) :
    out.objects = os ∧ out.covers = cv ∧ out.body = ⟨req.share, req.repo, us, os.map (·.id), cv⟩ ∧
      out.body.wellFormed = true := by
  dsimp only [finish] at h
  split at h
  · rename_i hw
    cases h
    simp only [Bool.and_eq_true] at hw
    exact ⟨rfl, rfl, rfl, hw.1⟩
  · cases h

/-- What a passing `prepare` checked: the limits, the objects, the update list, and the plain or
share checks. -/
theorem prepare_ok {t : Table} {req : PrepareReq} {out : Prepared} (h : prepare t req = .ok out) :
    limitsOk req = true ∧ ∃ os, checkObjectsE req.stream = .ok os ∧
      updatesError req (sortUpdates req.updates) = none ∧
      (req.share = false → checkPlain t req os (sortUpdates req.updates) = .ok out) ∧
      (req.share = true → checkShare t req os (sortUpdates req.updates) = .ok out) := by
  unfold prepare at h
  split at h
  · cases h
  · rename_i hl
    refine ⟨by simpa using hl, ?_⟩
    split at h
    · cases h
    · rename_i os hos
      refine ⟨os, hos, ?_⟩
      dsimp only at h
      cases hu : updatesError req (sortUpdates req.updates) with
      | some r => simp [hu] at h
      | none =>
        simp only [hu] at h
        refine ⟨rfl, fun hs => ?_, fun hs => ?_⟩ <;> simpa [hs] using h

/-- What a passing plain push checked. -/
theorem checkPlain_ok {t : Table} {req : PrepareReq} {os : Array Obj} {us : Array Update}
    {out : Prepared} (h : checkPlain t req os us = .ok out) :
    (t.complete = true ∨ ∀ o ∈ os, o.isRoot = false) ∧ (∀ o ∈ os, listed t o.id = false) ∧
      (∀ s ∈ checkedSeats req, gateOk t req (refsOutOf os us) s = true) ∧
      finish req os us #[] = .ok out := by
  dsimp only [checkPlain] at h
  split at h
  · cases h
  · rename_i hr
    split at h
    · cases h
    · rename_i hf
      split at h
      · cases h
      · rename_i hg
        refine ⟨?_, ?_, ?_, h⟩
        · simp only [Bool.not_eq_true', Bool.not_eq_false, Bool.or_eq_true, Array.all_eq_true,
            Bool.not_eq_true'] at hr
          rcases hr with hr | hr
          · exact .inl hr
          · refine .inr fun o ho => ?_
            obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp ho
            exact hr i hi
        · simp only [Bool.not_eq_true', Bool.not_eq_false, Array.all_eq_true,
            Bool.not_eq_true'] at hf
          intro o ho
          obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp ho
          exact hf i hi
        · simp only [Bool.not_eq_true', Bool.not_eq_false, Array.isEmpty_iff] at hg
          intro s hs
          refine Classical.byContradiction fun hne => ?_
          have : s ∈ (checkedSeats req).filter fun s => !gateOk t req (refsOutOf os us) s :=
            Array.mem_filter.mpr ⟨hs, by simpa using hne⟩
          rw [hg] at this
          simp at this

/-- **The root rule** (G-F1): a plain push carries a root commit only from a complete table. -/
theorem checkPush_root {t : Table} {req : PrepareReq} {out : Prepared}
    (h : prepare t req = .ok out) (hns : req.share = false) {o : Obj} (ho : o ∈ out.objects)
    (hk : o.kind = .commit) (hp : commitParents o = []) : t.complete = true := by
  obtain ⟨-, os, -, -, hpl, -⟩ := prepare_ok h
  obtain ⟨hr, -, -, hf⟩ := checkPlain_ok (hpl hns)
  obtain ⟨rfl, -⟩ := finish_ok hf
  rcases hr with hr | hr
  · exact hr
  · have := hr o ho
    simp [Obj.isRoot, hk, hp] at this

/-- **Freshness** (G-M6): a plain push carries no id that an entry lists. -/
theorem checkPush_fresh {t : Table} {req : PrepareReq} {out : Prepared}
    (h : prepare t req = .ok out) (hns : req.share = false) :
    ∀ o ∈ out.objects, ∀ e ∈ t.entries, o.id ∉ e.body.oids := by
  obtain ⟨-, os, -, -, hpl, -⟩ := prepare_ok h
  obtain ⟨-, hf, -, hfin⟩ := checkPlain_ok (hpl hns)
  obtain ⟨rfl, -⟩ := finish_ok hfin
  intro o ho e he hmem
  have := hf o ho
  simp only [listed, List.any_eq_false] at this
  exact absurd (Array.contains_iff_mem.mpr hmem) (by simpa using this e he)

/-- **The gate** (G-M1): every checked seat of a plain push is entitled to everything it builds
on, and is seated in an entry that assigned each value the push replaces, under the same name. -/
theorem checkPush_gate {t : Table} {req : PrepareReq} {out : Prepared}
    (h : prepare t req = .ok out) (hns : req.share = false) :
    ∀ s ∈ checkedSeats req, (∀ x ∈ refsOut out, entitled t s x) ∧
      ∀ u ∈ req.updates, ∀ v, u.old = some v →
        ∃ e ∈ t.entries, seated e s ∧ assigns e req.repo u.name (some v) := by
  obtain ⟨-, os, -, -, hpl, -⟩ := prepare_ok h
  obtain ⟨-, -, hg, hfin⟩ := checkPlain_ok (hpl hns)
  obtain ⟨rfl, -, hb, -⟩ := finish_ok hfin
  intro s hs
  have := hg s hs
  simp only [gateOk, Bool.and_eq_true, List.all_eq_true, Array.all_eq_true] at this
  refine ⟨fun x hx => ?_, fun u hu v hv => ?_⟩
  · simp only [refsOut, hb] at hx
    exact this.1 x hx
  · obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp hu
    have := this.2 i hi
    simp only [nameRuleOk, hv, List.any_eq_true, Bool.and_eq_true] at this
    exact this

/-- **G-F1**: what a plain push may carry. No id an entry lists; a root commit only from a
complete table; and every checked seat is entitled to everything it builds on. -/
theorem checkPush_history {t : Table} {req : PrepareReq} {out : Prepared}
    (h : prepare t req = .ok out) (hns : req.share = false) :
    (∀ o ∈ out.objects, ∀ e ∈ t.entries, o.id ∉ e.body.oids) ∧
    (t.complete = false → ∀ o ∈ out.objects, o.kind = .commit → commitParents o ≠ []) ∧
    ∀ s ∈ checkedSeats req, ∀ x ∈ refsOut out, entitled t s x :=
  ⟨checkPush_fresh h hns,
   fun hc o ho hk hp => by simp [checkPush_root h hns ho hk hp] at hc,
   fun s hs => (checkPush_gate h hns s hs).1⟩

/-! ### Shares -/

/-- What a passing share checked. -/
theorem checkShare_ok {t : Table} {req : PrepareReq} {os : Array Obj} {us : Array Update}
    {out : Prepared} (h : checkShare t req os us = .ok out) :
    let pre : Prepared := ⟨.empty, #[], #[], os, ⟨true, req.repo, us, os.map (·.id), #[]⟩⟩
    commitIds pre = newValues req ∧ (∀ x ∈ refsOut pre, x ∈ parentIds pre) ∧
      (∀ u ∈ req.updates, ∀ v, u.old = some v → u.new = some v) ∧
      (∀ s ∈ coversOf t req pre, keyChanged t s = false) ∧ coversOf t req pre = req.expect ∧
      finish req os us (coversOf t req pre) = .ok out := by
  intro pre
  dsimp only [checkShare] at h
  split at h
  · cases h
  · rename_i hx
    split at h
    · cases h
    · rename_i hk
      split at h
      · cases h
      · rename_i hc
        simp only [Bool.not_eq_true', Bool.not_eq_false, Bool.and_eq_true, beq_iff_eq,
          List.all_eq_true, Array.all_eq_true] at hx
        obtain ⟨⟨h1, h2⟩, h3⟩ := hx
        refine ⟨h1, fun x hx => by simpa using h2 x hx, fun u hu v hv => ?_, fun s hs => ?_,
          by simpa using hc, h⟩
        · obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp hu
          have := h3 i hi
          simp only [hv, Option.all_some, beq_iff_eq] at this
          exact this.symm
        · have hk' : ∀ x ∈ coversOf t req pre, keyChanged t x = false := by
            intro x hx
            refine Classical.byContradiction fun hne => hk ?_
            obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp hx
            exact Array.any_eq_true.mpr ⟨i, hi, by simpa using hne⟩
          exact hk' s hs

/-- `coversOf` reads only the carried objects. -/
theorem coversOf_objects {t : Table} {req : PrepareReq} {a b : Prepared}
    (h : a.objects = b.objects) : coversOf t req a = coversOf t req b := by
  simp [coversOf, h]

/-- **Exact shares** (G-M7): a share carries exactly the commits its updates name, and of their
history only their parents' ids; it moves no ref and deletes none; its covers are those the dialog
showed and exactly the checked seats it gives a listed object they were not entitled to; no
covered seat's key changed; and every checked seat it does not cover was already entitled to every
listed object it carries. -/
theorem checkShare_exact {t : Table} {req : PrepareReq} {out : Prepared}
    (h : prepare t req = .ok out) (hs : req.share = true) :
    commitIds out = newValues req ∧ (∀ x ∈ refsOut out, x ∈ parentIds out) ∧
    out.covers = req.expect ∧ out.covers = coversOf t req out ∧
    (∀ s ∈ out.covers, keyChanged t s = false) ∧
    ∀ s ∈ checkedSeats req, s ∉ out.covers →
      ∀ o ∈ out.objects, (∃ e ∈ t.entries, o.id ∈ e.body.oids) → entitled t s o.id := by
  obtain ⟨-, os, -, -, -, hsh⟩ := prepare_ok h
  obtain ⟨h1, h2, -, h4, h5, hfin⟩ := checkShare_ok (hsh hs)
  obtain ⟨hobj, hcov, hbody, -⟩ := finish_ok hfin
  have hco : coversOf t req out =
      coversOf t req ⟨.empty, #[], #[], os, ⟨true, req.repo, sortUpdates req.updates,
        os.map (·.id), #[]⟩⟩ := coversOf_objects hobj
  refine ⟨?_, ?_, hcov.trans h5, hcov.trans hco.symm, fun s hs' => h4 s (hcov ▸ hs'), ?_⟩
  · simpa [commitIds, hobj] using h1
  · intro x hx
    have := h2 x (by simpa [refsOut, hobj, hbody] using hx)
    simpa [parentIds, hobj] using this
  · intro s hs' hnc o ho hl
    rw [hcov, ← hco] at hnc
    refine Classical.byContradiction fun hne => hnc ?_
    refine Array.mem_filter.mpr ⟨hs', ?_⟩
    obtain ⟨e, he, hoe⟩ := hl
    refine Array.any_eq_true.mpr ?_
    obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp ho
    refine ⟨i, hi, ?_⟩
    simp only [listed, Bool.and_eq_true, List.any_eq_true, Bool.not_eq_true']
    exact ⟨⟨e, he, Array.contains_iff_mem.mpr hoe⟩, by simpa using hne⟩

/-! ### The view -/

/-- **The push log** is exactly every update of every entry of the repository. -/
theorem pushLog_spec {t : Table} {repo : String} {x : LogEntry} :
    x ∈ (gitView t repo).log ↔ ∃ e ∈ t.entries, e.body.repo = repo ∧
      ∃ u ∈ e.body.updates, x = ⟨e.digest, e.author, e.body.share, u⟩ := by
  simp only [gitView, List.mem_mergeSort, List.mem_flatMap, List.mem_filter, List.mem_map,
    Array.mem_toList_iff, beq_iff_eq]
  constructor
  · rintro ⟨e, ⟨he, hr⟩, u, hu, rfl⟩
    exact ⟨e, he, hr, u, hu, rfl⟩
  · rintro ⟨e, he, hr, u, hu, rfl⟩
    exact ⟨e, ⟨he, hr⟩, u, hu, rfl⟩

/-- **The register**: the live assignments are exactly the assignments that no entry which saw
them replaced. -/
theorem refs_spec {t : Table} {repo n : String} {d : Digest} {v : Option Oid} :
    (n, d, v) ∈ (gitView t repo).refs ↔ ∃ e ∈ t.entries, e.digest = d ∧ assigns e repo n v ∧
      ¬ ∃ f ∈ t.entries, (∃ u ∈ f.body.updates, f.body.repo = repo ∧ u.name = n ∧ u.old = v) ∧
        d ∈ t.reach f := by
  simp only [gitView, List.mem_mergeSort, List.mem_filter, List.mem_flatMap, List.mem_map,
    Array.mem_toList_iff, beq_iff_eq, Bool.not_eq_true', superseded, List.any_eq_false,
    Bool.and_eq_true, Array.any_eq_true, Std.ExtTreeSet.contains_iff_mem, assigns, Prod.mk.injEq]
  constructor
  · rintro ⟨⟨e, ⟨he, hr⟩, u, hu, rfl, rfl, rfl⟩, hns⟩
    refine ⟨e, he, rfl, ⟨hr, ?_⟩, ?_⟩
    · obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp hu
      exact ⟨i, hi, by simp⟩
    · rintro ⟨f, hf, ⟨u', hu', hr', hn', ho'⟩, hd⟩
      refine hns f hf ⟨?_, hd⟩
      obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp hu'
      exact ⟨i, hi, by simp [hr', hn', ho']⟩
  · rintro ⟨e, he, rfl, ⟨hr, i, hi, hu⟩, hns⟩
    refine ⟨⟨e, ⟨he, hr⟩, e.body.updates[i], Array.getElem_mem hi, hu.1, rfl, hu.2⟩, ?_⟩
    intro f hf ⟨⟨j, hj, hu'⟩, hd⟩
    exact hns ⟨f, hf, ⟨_, Array.getElem_mem hj, hu'.1.1, hu'.1.2, hu'.2⟩, hd⟩

/-! ### The ops -/

/-- What the channel checks refuse with. -/
theorem channelError_some {ch : Proto.Chat} {sg : GroupId} {hs : Array (Digest × ByteArray)}
    {r : Reply} (h : channelError ch sg hs = some r) :
    r = .refused (.badApp .notStored) ∨ r = .code .badOpening ∨ ∃ ds, r = .openingsMissing ds := by
  unfold channelError at h
  dsimp only at h
  split at h
  · cases h; exact .inl rfl
  · split at h
    · cases h; exact .inr (.inl rfl)
    · split at h
      · cases h
      · cases h; exact .inr (.inr ⟨_, rfl⟩)

/-- `GIT_PREPARE`'s `OK` is `prepare` of the channel's table. -/
theorem run_git_prepare {s : State} {p : PrepareReq} {r : Reply} (h : run s (.prepare p) = r) :
    ∀ out, r = .prepared out → ∃ ch, s.chats[p.channelKey]? = some ch ∧
      prepare (tableOf ch p.helds) p = .ok out := by
  intro out hr
  subst hr
  simp only [run] at h
  split at h
  · cases h
  · rename_i ch hch
    refine ⟨ch, hch, ?_⟩
    split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · rename_i r hr
          subst h
          rcases channelError_some hr with h | h | ⟨_, h⟩ <;> cases h
        · split at h
          · rename_i out' hout; cases h; exact hout
          · cases h

/-- `GIT_VIEW`'s `OK` is the view of the channel's table. -/
theorem run_git_view {s : State} {sg : GroupId} {ck repo : String}
    {hs : Array (Digest × ByteArray)} {v : View} (h : run s (.view sg ck repo hs) = .view v) :
    ∃ ch, s.chats[ck]? = some ch ∧ v = gitView (tableOf ch hs) repo := by
  simp only [run] at h
  split at h
  · cases h
  · rename_i ch hch
    refine ⟨ch, hch, ?_⟩
    split at h
    · rename_i r hr
      subst h
      rcases channelError_some hr with h | h | ⟨_, h⟩ <;> cases h
    · cases h; rfl

/-- `GIT_OBJECTS`'s `OK`: the piece key is bound to a git push, the stream passes every piece,
`checkObjects` accepts it, and its ids are exactly those the push listed. -/
theorem run_git_objects {s : State} {key : String} {st : ByteArray} {os : Array Obj}
    (h : run s (.objects key st) = .objects os) :
    ∃ ctx b, s.ctxs[key]? = some ctx ∧ ctx.header.app = appGit ∧ assembleOk ctx st = true ∧
      checkObjects st = some os ∧ parseBody ctx.header.body = some b ∧ os.map (·.id) = b.oids := by
  simp only [run] at h
  split at h
  · cases h
  · rename_i ctx hctx
    split at h
    · cases h
    · rename_i happ
      split at h
      · cases h
      · rename_i hasm
        split at h
        · cases h
        · rename_i os' hos
          split at h
          · cases h
          · rename_i b hb
            split at h
            · rename_i hids
              cases h
              exact ⟨ctx, b, hctx, Decidable.not_not.mp happ, by simpa using hasm,
                by simp [checkObjects, hos], hb, hids⟩
            · cases h

/-! ### Raw objects: `parseRaw` inverts `rawOf` -/

theorem splitAt?_append {b : UInt8} {p q : List UInt8} (hp : ∀ x ∈ p, x ≠ b) :
    splitAt? b (p ++ b :: q) = some (p, q) := by
  induction p with
  | nil => simp [splitAt?]
  | cons x xs ih =>
    have hx : x ≠ b := hp x (List.mem_cons_self ..)
    simp [splitAt?, hx, ih fun y hy => hp y (List.mem_cons_of_mem _ hy)]

/-- The digits of `0` to `9`. -/
theorem digit_spec : ∀ m, m < 10 → isDigit (48 + m).toUInt8 = true ∧ ((48 + m).toUInt8).toNat = 48 + m := by
  decide

/-- What `decDigits` writes: decimal digits, not empty, whose value is `n`, with no leading zero. -/
theorem decDigits_spec (n : Nat) : decDigits n ≠ [] ∧ (∀ x ∈ decDigits n, isDigit x = true) ∧
    decValue (decDigits n) = n ∧ (1 ≤ n → (decDigits n).head? ≠ some 48) := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    rw [decDigits]
    split
    · rename_i hn
      obtain ⟨h1, h2⟩ := digit_spec n hn
      refine ⟨by simp, by simpa using h1, ?_, fun h1n => ?_⟩
      · simp only [decValue, List.foldl_cons, List.foldl_nil, h2]
        omega
      · simp only [List.head?_cons, ne_eq, Option.some.injEq]
        intro he
        have := congrArg UInt8.toNat he
        rw [h2] at this
        simp at this
        omega
    · rename_i hn
      obtain ⟨ih1, ih2, ih3, ih4⟩ := ih (n / 10) (by omega)
      obtain ⟨h1, h2⟩ := digit_spec (n % 10) (Nat.mod_lt _ (by omega))
      refine ⟨by simp, fun x hx => ?_, ?_, fun _ => ?_⟩
      · rcases List.mem_append.mp hx with hx | hx
        · exact ih2 x hx
        · simp only [List.mem_singleton] at hx
          exact hx ▸ h1
      · simp only [decValue, List.foldl_append, List.foldl_cons, List.foldl_nil] at ih3 ⊢
        rw [ih3, h2]
        omega
      · rw [List.head?_append]
        obtain ⟨y, ys, hy⟩ := List.exists_cons_of_ne_nil ih1
        have := ih4 (by omega)
        rw [hy] at this ⊢
        simpa using this

theorem validDec_decDigits (n : Nat) : validDec (decDigits n) = true := by
  obtain ⟨h1, h2, -, h4⟩ := decDigits_spec n
  simp only [validDec, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff, ne_eq,
    h1, not_false_eq_true, List.all_eq_true, Bool.or_eq_true, beq_iff_eq, bne_iff_ne, true_and]
  refine ⟨h2, ?_⟩
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · left; rw [decDigits]; simp
  · exact .inr (h4 hn)

theorem kindOfWord_word (k : Kind) : kindOfWord k.word = .ok k := by
  cases k <;> rfl

theorem parseHeaderL_headerL (k : Kind) (n : Nat) (rest : List UInt8) :
    parseHeaderL (headerL k n ++ rest) = .ok (k, n, (headerL k n).length) := by
  have hw : ∀ x ∈ k.word, x ≠ 32 := by cases k <;> decide
  have hd : ∀ x ∈ decDigits n, x ≠ 0 := fun x hx he => by
    have := (decDigits_spec n).2.1 x hx
    subst he
    simp [isDigit] at this
  have e : headerL k n ++ rest = k.word ++ 32 :: (decDigits n ++ 0 :: rest) := by
    simp [headerL]
  rw [e]
  simp only [parseHeaderL, splitAt?_append hw, kindOfWord_word, splitAt?_append hd,
    validDec_decDigits, (decDigits_spec n).2.2.1, ↓reduceIte]
  simp [headerL]
  omega

theorem size_mk (l : List UInt8) : (⟨l.toArray⟩ : ByteArray).size = l.length := by
  simp [ByteArray.size]

/-- **The raw form is an injective encoding**: `parseRaw` reads back the kind and the content. -/
theorem parseRaw_rawOf (k : Kind) (c : ByteArray) : parseRaw (rawOf k c) = some (k, c) := by
  have hl : (rawOf k c).data.toList = headerL k c.size ++ c.data.toList := by
    simp [rawOf]
  have hs : (rawOf k c).size = (headerL k c.size).length + c.size := by
    simp [rawOf, size_mk]
  simp only [parseRaw, hl, parseHeaderL_headerL, hs, ↓reduceIte]
  congr
  exact ByteArray.extract_append_eq_right (by simp [size_mk]) (by simp [size_mk])

/-! ### The push body: `parseBody` inverts `writeBody` -/

theorem toNat_toUInt8 {n : Nat} (h : n < 256) : n.toUInt8.toNat = n := by
  simp [Nat.toUInt8]; omega

theorem lpTake_append (l r : List UInt8) : lpTake l.length (l ++ r) = some (l, r) := by
  simp [lpTake]

theorem lpTake_eq {n : Nat} {l : List UInt8} (h : l.length = n) (r : List UInt8) :
    lpTake n (l ++ r) = some (l, r) := h ▸ lpTake_append l r

theorem mk_data (b : ByteArray) : (⟨b.data⟩ : ByteArray) = b := rfl

theorem lpU16_u16L {n : Nat} (h : n < 65536) (r : List UInt8) : lpU16 (u16L n ++ r) = some (n, r) := by
  simp only [u16L, List.cons_append, List.nil_append, lpU16, Option.some.injEq, Prod.mk.injEq,
    and_true]
  rw [toNat_toUInt8 (by omega)]
  simp [Nat.toUInt8]
  omega

theorem lpOid_oidL (o : Oid) (r : List UInt8) : lpOid (oidL o ++ r) = some (o, r) := by
  have hl : (oidL o).length = 32 := by simp [oidL, o.size_eq]
  simp only [lpOid, lpTake_eq hl]
  simp [oidL, mk_data]

theorem lpOptOid_optOidL (o : Option Oid) (r : List UInt8) :
    lpOptOid (optOidL o ++ r) = some (o, r) := by
  cases o with
  | none => rfl
  | some o => simp [optOidL, lpOptOid, lpOid_oidL]

theorem lpFlag_flagL (b : Bool) (r : List UInt8) : lpFlag (flagL b :: r) = some (b, r) := by
  cases b <;> rfl

theorem fromUTF8_toUTF8 (s : String) : String.fromUTF8? ⟨s.toUTF8.data.toList.toArray⟩ = some s := by
  simp [String.fromUTF8?, s.isValidUTF8, String.fromUTF8]

theorem lpName_nameL {s : String} (h : s.toUTF8.size < 256) (r : List UInt8) :
    lpName (nameL s ++ r) = some (s, r) := by
  have hl : s.toUTF8.data.toList.length = s.toUTF8.size.toUInt8.toNat := by
    rw [toNat_toUInt8 h, Array.length_toList]; rfl
  unfold nameL
  rw [List.cons_append]
  unfold lpName
  dsimp only
  rw [lpTake_eq hl]
  dsimp only
  rw [fromUTF8_toUTF8]
  rfl

theorem lpUpdate_updateL {u : Update} (h : u.name.toUTF8.size < 256) (r : List UInt8) :
    lpUpdate (updateL u ++ r) = some (u, r) := by
  simp only [updateL, List.append_assoc, lpUpdate, lpName_nameL h, lpOptOid_optOidL,
    List.singleton_append, lpFlag_flagL]

theorem lpSeat_seatL {s : Serve.Seat} (h : s.tag.size = 16) (r : List UInt8) :
    lpSeat (seatL s ++ r) = some (s, r) := by
  have ha : s.aci.bytes.data.toList.length = 16 := by simp [s.aci.size_eq]
  have ht : s.tag.toList.length = 16 := by simp [h]
  simp only [seatL, List.append_assoc, lpSeat, lpTake_eq ha, lpTake_eq ht]
  simp [mk_data]

theorem lpMany_flatMap {α : Type} {p : LP α} {w : α → List UInt8}
    (hp : ∀ x r, p (w x ++ r) = some (x, r)) :
    ∀ (xs : List α) (r : List UInt8), lpMany p xs.length (xs.flatMap w ++ r) = some (xs, r)
  | [], r => rfl
  | x :: xs, r => by
    simp only [List.length_cons, List.flatMap_cons, List.append_assoc, lpMany, hp,
      lpMany_flatMap hp xs]

theorem lpMany_flatMap' {α : Type} {p : LP α} {w : α → List UInt8} {P : α → Prop}
    (hp : ∀ x, P x → ∀ r, p (w x ++ r) = some (x, r)) :
    ∀ (xs : List α), (∀ x ∈ xs, P x) → ∀ (r : List UInt8),
      lpMany p xs.length (xs.flatMap w ++ r) = some (xs, r)
  | [], _, r => rfl
  | x :: xs, hx, r => by
    simp only [List.length_cons, List.flatMap_cons, List.append_assoc, lpMany,
      hp x (hx x (List.mem_cons_self ..)),
      lpMany_flatMap' hp xs (fun y hy => hx y (List.mem_cons_of_mem _ hy))]

/-- The body's fields read back from its bytes, when it is within the limits. -/
theorem parseBodyL_writeBodyL {b : Body} (hw : b.wellFormed = true) :
    parseBodyL (writeBodyL b) = some b := by
  simp only [Body.wellFormed, Bool.and_eq_true, decide_eq_true_eq, Array.all_eq_true] at hw
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hrepo, -⟩, hus⟩, huw⟩, -⟩, hos⟩, -⟩, hcs⟩, hct⟩, -⟩, -⟩ := hw
  have hun : ∀ u ∈ b.updates.toList, u.name.toUTF8.size < 256 := by
    intro u hu
    obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp (Array.mem_toList_iff.mp hu)
    have := huw i hi
    simp [Update.wellFormed, maxRefName] at this ⊢
    omega
  have hct' : ∀ c ∈ b.covers.toList, c.tag.size = 16 := by
    intro c hc
    obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp (Array.mem_toList_iff.mp hc)
    simpa using hct i hi
  have hnu : (b.updates.size.toUInt8).toNat = b.updates.toList.length := by
    rw [toNat_toUInt8 (by simp only [maxUpdates] at hus; omega)]; simp
  have hrepo' : b.repo.toUTF8.size < 256 := by simp only [maxRepoName] at hrepo; omega
  have hos' : b.oids.size < 65536 := by simp only [maxObjects] at hos; omega
  have hcs' : b.covers.size < 65536 := by simp only [Serve.maxAudience] at hcs; omega
  unfold parseBodyL writeBodyL
  rw [lpTake_eq (n := 5) (l := bodyTagL) rfl]
  simp only [ne_eq, not_true_eq_false, ↓reduceIte, lpFlag_flagL, lpName_nameL hrepo', lpU8, hnu,
    lpMany_flatMap' (fun u hu r => lpUpdate_updateL hu r) _ hun, lpU16_u16L hos']
  rw [show b.oids.size = b.oids.toList.length by simp, lpMany_flatMap lpOid_oidL]
  simp only [lpU16_u16L hcs']
  rw [show b.covers.size = b.covers.toList.length by simp,
    show b.covers.toList.flatMap seatL = b.covers.toList.flatMap seatL ++ [] by simp,
    lpMany_flatMap' (fun c hc r => lpSeat_seatL hc r) _ hct']
  simp

/-- **The body round trip**: a well-formed body reads back from its bytes. -/
theorem parseBody_writeBody {b : Body} (hw : b.wellFormed = true) :
    parseBody (writeBody b) = some b := by
  have hl : (writeBody b).data.toList = writeBodyL b := by simp [writeBody]
  simp [parseBody, hl, parseBodyL_writeBodyL hw, hw]

/-- **The body is canonical**: the bytes `parseBody` reads are exactly those `writeBody` writes
for what it read. So a push record's meaning is unique. -/
theorem writeBody_parseBody {x : ByteArray} {b : Body} (h : parseBody x = some b) :
    writeBody b = x := by
  unfold parseBody at h
  split at h
  · split at h
    · rename_i hc
      cases h
      exact hc.2
    · cases h
  · cases h

/-! ### Equal stores and openings give equal views -/

/-- **One commit, one opening**: two openings that match one commitment (one author, one group)
are equal, or SHA-256 has a collision. -/
theorem opening_unique {g : GroupId} {a : Aci} {c : Digest} {o₁ o₂ : ByteArray}
    (h₁ : openingMatches g a c o₁ = true) (h₂ : openingMatches g a c o₂ = true) :
    o₁ = o₂ ∨ ∃ x y : ByteArray, x ≠ y ∧ sha256 x = sha256 y := by
  obtain ⟨n₁, m₁, rfl, hb₁, hc₁⟩ := openingMatches_spec h₁
  obtain ⟨n₂, m₂, rfl, hb₂, hc₂⟩ := openingMatches_spec h₂
  simp only [commit, hb₁, hb₂, Option.map_some, Option.some.injEq] at hc₁ hc₂
  let P := commitTag ++ g.bytes ++ a.bytes
  have e₁ : commitTag ++ g.bytes ++ a.bytes ++ n₁.bytes ++ m₁ = P ++ (n₁.bytes ++ m₁) :=
    ByteArray.append_assoc
  have e₂ : commitTag ++ g.bytes ++ a.bytes ++ n₂.bytes ++ m₂ = P ++ (n₂.bytes ++ m₂) :=
    ByteArray.append_assoc
  rw [e₁] at hc₁
  rw [e₂] at hc₂
  by_cases hx : P ++ (n₁.bytes ++ m₁) = P ++ (n₂.bytes ++ m₂)
  · exact .inl ((ByteArray.append_right_inj P).1 hx)
  · exact .inr ⟨_, _, hx, hc₁.trans hc₂.symm⟩

/-- `heldFor` returns a held opening that matches the record. -/
theorem heldFor_spec {hs : Array (Digest × ByteArray)} {d : Digest} {r : Rec} {o : ByteArray}
    (h : heldFor hs d r = some o) :
    (d, o) ∈ hs ∧ openingMatches r.group r.author r.commit o = true := by
  unfold heldFor at h
  cases hf : hs.find? (fun (d', o) => d' == d && openingMatches r.group r.author r.commit o) with
  | none => simp [hf] at h
  | some x =>
    simp only [hf, Option.map_some, Option.some.injEq] at h
    subst h
    have hm := Array.mem_of_find?_eq_some hf
    have hp := Array.find?_some hf
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    obtain ⟨d', o'⟩ := x
    simp only at hp ⊢
    exact ⟨hp.1 ▸ hm, hp.2⟩

/-- `heldFor` finds an opening when one is held. -/
theorem heldFor_some {hs : Array (Digest × ByteArray)} {d : Digest} {r : Rec}
    (h : ∃ o, (d, o) ∈ hs ∧ openingMatches r.group r.author r.commit o = true) :
    ∃ o, heldFor hs d r = some o := by
  obtain ⟨o, ho, hm⟩ := h
  have : (hs.find? fun (d', o) => d' == d && openingMatches r.group r.author r.commit o).isSome :=
    Array.find?_isSome.mpr ⟨(d, o), ho, by simp [hm]⟩
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp this
  exact ⟨x.2, by simp [heldFor, hx]⟩

theorem filterMap_congr' {α β : Type} {f g : α → Option β} :
    ∀ {l : List α}, (∀ x ∈ l, f x = g x) → l.filterMap f = l.filterMap g
  | [], _ => rfl
  | x :: xs, h => by
    simp only [List.filterMap_cons, h x (List.mem_cons_self ..),
      filterMap_congr' fun y hy => h y (List.mem_cons_of_mem _ hy)]

theorem all_congr' {α : Type} {f g : α → Bool} :
    ∀ {l : List α}, (∀ x ∈ l, f x = g x) → l.all f = l.all g
  | [], _ => rfl
  | x :: xs, h => by
    simp only [List.all_cons, h x (List.mem_cons_self ..),
      all_congr' fun y hy => h y (List.mem_cons_of_mem _ hy)]

/-- The table is a function of the records and the openings `heldFor` picks. -/
theorem tableOfMap_congr {m : RecMap} {cl : Bool} {h₁ h₂ : Array (Digest × ByteArray)}
    (h : ∀ k r, m[k]? = some r → heldFor h₁ k r = heldFor h₂ k r) :
    tableOfMap m cl h₁ = tableOfMap m cl h₂ := by
  have h' : ∀ x ∈ m.toList, heldFor h₁ x.1 x.2 = heldFor h₂ x.1 x.2 := fun x hx =>
    h x.1 x.2 (Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some.mp hx)
  simp only [tableOfMap]
  rw [filterMap_congr' fun x hx => by rw [h' x hx], all_congr' fun x hx => by rw [h' x hx]]

/-- **Equal stores, complete openings, equal views.** Two stores with the same records, each with
a held opening for every record, give every repository the same view, or SHA-256 has a collision
(two different openings of one record). -/
theorem gitView_congr {c d : CheckedStore} {hc hd : Array (Digest × ByteArray)} (repo : String)
    (hm : c.raw.map = d.raw.map) (hcc : Complete c hc) (hdc : Complete d hd) :
    gitView (tableOfStore c hc) repo = gitView (tableOfStore d hd) repo ∨
      ∃ x y : ByteArray, x ≠ y ∧ sha256 x = sha256 y := by
  by_cases hall : ∀ k r, c.raw.map[k]? = some r → heldFor hc k r = heldFor hd k r
  · left
    simp only [tableOfStore, ← hm]
    rw [tableOfMap_congr hall]
  · right
    have : ∃ k r, c.raw.map[k]? = some r ∧ heldFor hc k r ≠ heldFor hd k r :=
      Classical.byContradiction fun hn => hall fun k r hk =>
        Classical.byContradiction fun hne => hn ⟨k, r, hk, hne⟩
    obtain ⟨k, r, hk, hne⟩ := this
    obtain ⟨o₁, h₁⟩ := heldFor_some (hcc k r hk)
    obtain ⟨o₂, h₂⟩ := heldFor_some (hdc k r (hm ▸ hk))
    rcases opening_unique (heldFor_spec h₁).2 (heldFor_spec h₂).2 with he | hcol
    · exact absurd (by rw [h₁, h₂, he]) hne
    · exact hcol

/-! ## Examples: objects of a real SHA-256 repository

The objects of the git beat (BUILD_M1 §A.2), written here and pinned against
`git init --object-format=sha256` (git 2.43): each id below is the one `git hash-object`,
`git mktree` and `git commit-tree` print for the same content (dates `1730419200 +0000`). -/

namespace Beat

/-- A tree entry: `<mode> SP <name> NUL <id>`. -/
def entry (mode name : String) (id : Oid) : ByteArray := (mode ++ " " ++ name).toUTF8 ++ ⟨#[0]⟩ ++ id.bytes

/-- A tree's content from its entries, in the order given. -/
def treeOf (es : List (String × String × Oid)) : ByteArray :=
  es.foldl (fun acc (m, n, o) => acc ++ entry m n o) .empty

/-- A commit's content: tree, parents, author and committer (same person and date), message. -/
def commitOf (tree : Oid) (parents : List Oid) (who : String) (msg : String) : ByteArray :=
  let ident := who ++ " <" ++ who.toLower ++ "@example.org> 1730419200 +0000\n"
  ("tree " ++ tree.toHex ++ "\n" ++ String.join (parents.map fun p => "parent " ++ p.toHex ++ "\n") ++
    "author " ++ ident ++ "committer " ++ ident ++ "\n" ++ msg ++ "\n").toUTF8

/-- An object's id. -/
def idOf (k : Kind) (c : ByteArray) : Oid := sha256 (rawOf k c)

/-- `README.md`: `hello`. -/
def bReadme : ByteArray := "hello\n".toUTF8
/-- `a.txt` in c1. -/
def bA : ByteArray := "a\n".toUTF8
/-- `a.txt` in c2. -/
def bA2 : ByteArray := "a2\n".toUTF8
/-- `c.txt` in c3. -/
def bC : ByteArray := "c\n".toUTF8
/-- `a/main.c` in c3. -/
def bMain : ByteArray := "int main;\n".toUTF8
/-- `d.txt` in Dave's own repository. -/
def bD : ByteArray := "d\n".toUTF8

/-- c0's tree. -/
def t0 : ByteArray := treeOf [("100644", "README.md", idOf .blob bReadme)]
/-- c1's tree. -/
def t1 : ByteArray := treeOf [("100644", "README.md", idOf .blob bReadme), ("100644", "a.txt", idOf .blob bA)]
/-- c2's tree. -/
def t2 : ByteArray := treeOf [("100644", "README.md", idOf .blob bReadme), ("100644", "a.txt", idOf .blob bA2)]
/-- The subdirectory `a` of c3. -/
def tS : ByteArray := treeOf [("100755", "main.c", idOf .blob bMain)]
/-- c3's tree: `a.txt` sorts before the directory `a` (git compares `a/`). -/
def t3 : ByteArray := treeOf [("100644", "README.md", idOf .blob bReadme),
  ("100644", "a.txt", idOf .blob bA2), ("40000", "a", idOf .tree tS), ("100644", "c.txt", idOf .blob bC)]
/-- d0's tree. -/
def tD : ByteArray := treeOf [("100644", "d.txt", idOf .blob bD)]

/-- Alice's root commit. -/
def c0 : ByteArray := commitOf (idOf .tree t0) [] "Alice" "c0"
/-- Alice's second commit. -/
def c1 : ByteArray := commitOf (idOf .tree t1) [idOf .commit c0] "Alice" "c1"
/-- Bob's amend of c1 (parent c0). -/
def c2 : ByteArray := commitOf (idOf .tree t2) [idOf .commit c0] "Bob" "c2 (amends c1)"
/-- Carol's commit on c2. -/
def c3 : ByteArray := commitOf (idOf .tree t3) [idOf .commit c2] "Carol" "c3"
/-- Dave's root commit of another repository. -/
def d0 : ByteArray := commitOf (idOf .tree tD) [] "Dave" "d0"

-- The ids git computes for the same objects.
#guard [idOf .blob bReadme, idOf .blob bA, idOf .blob bA2, idOf .blob bC, idOf .blob bMain,
    idOf .blob bD, idOf .tree t0, idOf .tree t1, idOf .tree t2, idOf .tree tS, idOf .tree t3,
    idOf .tree tD, idOf .commit c0, idOf .commit c1, idOf .commit c2, idOf .commit c3,
    idOf .commit d0].map (·.toHex) ==
  ["2cf8d83d9ee29543b34a87727421fdecb7e3f3a183d337639025de576db9ebb4",
   "f8625e43f9e04f24291f77cdbe4c71b3c2a3b0003f60419b3ed06a058d766c8b",
   "29a7c2dc7a756860c6c11980ee99f2836f37b1ac04f011403a73a133fd9c7e80",
   "2abe107e3b1b618efafa0df5e5f1118e5bf86694eb8c185741e67795ae314aa4",
   "29842569da6ae1369061c177365c50f42c314586094120aa8321ad3e4b2e6350",
   "22953182a5237cceb2e7b66cc7fa187f4048341b0b7d49a53d3942917d87ef69",
   "422950a7e508e04a1a72c95d6e167ccc83d1e2e8829ed2039dc2b9066a7bdae3",
   "95a7bb5a6b6eee3ff6f04de7fbba17928a31fc4c143177509165713675eef66f",
   "25379fec8d0d1384e6fe2e3292184d5c8686f04b44d0c2cc17318f3ac1d1fc1f",
   "5ec3009c561af7191ae296892ff83db7cb4e42318a8c4a3ca06ba6b60d45c160",
   "0d7a76484112c2554af6dd3a9ac315a929eb232b01cee0eb7e07ec44435890a2",
   "c3fff02489285bea29408c3e65f6052f8371d1f111513877b6beaa0ec6ed1d22",
   "9b895fb1f663404aa08d34683f61fd263998766427d238cd28aa8804319c0f70",
   "abd00b702cce89d666f5834a67f5dd197b8cb61ac888aee89f299f8c105e1354",
   "b826c7c6426b58d9df5092e64343e393d08a4d8bc5997a3326096848d76e14f9",
   "d7de50f954ba9960b7c72cd179371daa9d65a1bc0a86aa6afad953d3634532b0",
   "557ccc283198e27441ce80753d1850d830606bc9098c3287a29ac81f32128a87"]

/-- A push's stream: the raw objects, sorted by id. -/
def streamOf (os : List (Kind × ByteArray)) : ByteArray :=
  ((os.map fun (k, c) => (idOf k c, rawOf k c)).mergeSort fun a b => compare a.1 b.1 != .gt).foldl
    (fun acc (_, r) => acc ++ r) .empty

/-- P1 (Alice): c0, c1 and their trees and blobs. -/
def p1Stream : ByteArray :=
  streamOf [(.blob, bReadme), (.blob, bA), (.tree, t0), (.tree, t1), (.commit, c0), (.commit, c1)]
/-- P2 (Bob): c2, its tree and its new blob. -/
def p2Stream : ByteArray := streamOf [(.blob, bA2), (.tree, t2), (.commit, c2)]
/-- S (Alice shares main@c2): c2, its tree and both its blobs. -/
def sStream : ByteArray := streamOf [(.blob, bReadme), (.blob, bA2), (.tree, t2), (.commit, c2)]
/-- P3 (Carol): c3, its trees and its new blobs. -/
def p3Stream : ByteArray :=
  streamOf [(.blob, bC), (.blob, bMain), (.tree, tS), (.tree, t3), (.commit, c3)]
/-- Dave's root push of another repository. -/
def dStream : ByteArray := streamOf [(.blob, bD), (.tree, tD), (.commit, d0)]
/-- Bob's re-push of c1, which P1 carried. -/
def oldStream : ByteArray := streamOf [(.blob, bA), (.tree, t1), (.commit, c1)]

end Beat

open Beat in
#guard (checkObjects p1Stream).map (fun os => (os.map (·.id)).toList) ==
  some ([idOf .blob bReadme, idOf .blob bA, idOf .tree t0, idOf .tree t1, idOf .commit c0,
    idOf .commit c1].mergeSort fun a b => compare a b != .gt)
open Beat in
#guard (checkObjects p3Stream).map (fun os => os.toList.map refsOf |>.flatten |>.length) == some 7
open Beat in
#guard (checkObjects p1Stream).map (fun os => os.toList.filter (·.isRoot) |>.map (·.id)) ==
  some [idOf .commit c0]

end Zrdt.Git
