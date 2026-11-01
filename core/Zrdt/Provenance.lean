import Zrdt.Store

/-!
# Who confirmed a record (docs/PLAN.md §3.5, `CLASSIFY`)

The app records how each record reached this device (its provenance):

- `live`: Signal delivered it and the sender was the record's author, or this device sent it;
- `relayed`: another member passed it on;
- `imported`: it came from a dump, or from "keep what verifies".

Only live records count here, because only for them does Signal vouch for the author. A live
record also carries its author's disown list: the records in the author's name that the author
says it did not write.

`classify` gives every stored record one status. A record `r` with author `A`:

- `confirmedByAuthor`: some live record of `A` reaches `r` (by following links, `r` included),
  and no live record of `A` disowns `r`;
- `notConfirmedByAuthor`: a live record of `A` disowns `r`; or no live record of `A` reaches `r`
  while `A` has a live record that `r` does not reach either (the two were written in parallel,
  so `A` wrote after `r` existed and did not link it);
- `heldBy x`: a live record of another member `x` reaches `r` (if several do, the smallest `x` in
  byte order);
- `unconfirmed`: no live record reaches `r`.

When more than one applies, the first in this list wins. The status depends only on the links and
the facts, never on the order records arrived in, so the server cannot change it by reordering.

Only `live` matters among the provenances, so `relayed` and `imported` records are treated the
same way here; the app shows them differently.
-/

namespace Zrdt

/-- How a record reached this device. This is host state, trusted (docs/PLAN.md §3.5). -/
inductive Provenance
  /-- Signal delivered it with the record's author as the sender, or this device sent it. -/
  | live
  /-- Member `relayer` passed it on. -/
  | relayed (relayer : Aci)
  /-- It came from a dump or from "keep what verifies". -/
  | imported
deriving DecidableEq, Repr

/-- What the host tells `classify` about one record. -/
structure Fact where
  /-- The record's digest. -/
  digest : Digest
  /-- How it arrived. -/
  provenance : Provenance
  /-- For a live record: the records in its author's name that the author did not write. Ignored
  for other records. -/
  disown : Array Digest
deriving Repr

/-- A record's status (the four values above). -/
inductive Status
  /-- A live record of the author reaches it, and the author does not disown it. -/
  | confirmedByAuthor
  /-- The author disowns it, or wrote in parallel with it without linking it. -/
  | notConfirmedByAuthor
  /-- A live record of member `aci`, not the author, reaches it. -/
  | heldBy (aci : Aci)
  /-- No live record reaches it. -/
  | unconfirmed
deriving DecidableEq, Repr

/-- The live records, each with its disown list. A digest is live if any fact for it says so; if
several facts give it disown lists, they are joined. -/
def liveFacts (facts : Array Fact) : Std.ExtTreeMap Digest (Array Digest) compare :=
  facts.foldl (init := ∅) fun m f =>
    match f.provenance with
    | .live => m.insert f.digest (m.getD f.digest #[] ++ f.disown)
    | _ => m

open Examples in
#guard (liveFacts #[⟨dig 1, .live, #[dig 9]⟩, ⟨dig 2, .imported, #[dig 8]⟩,
  ⟨dig 1, .relayed alice, #[]⟩]).toList == [(dig 1, #[dig 9])]

/-- For every stored record, the stored records that link it (links followed backwards). Every
stored digest is a key, with `[]` if nothing links it. -/
def linkedBy (c : CheckedStore) : Std.ExtTreeMap Digest (List Digest) compare :=
  c.raw.map.foldl (init := c.raw.map.map fun _ _ => []) fun m d r =>
    r.links.foldl (init := m) fun m l => m.modify l (d :: ·)

/-- The stored records that reach `d` by following links (`d` included): `walk` backwards. -/
def reachersOf (back : Std.ExtTreeMap Digest (List Digest) compare) (d : Digest) : DigestSet :=
  walk id back ∅ [d]

/-- The records that reach every one of the given live records of one author. Only the newest of
them matter: the ones no other of them reaches (`newest`). A record that reaches those reaches
the rest too, since reaching is transitive. `none` if `newest` is empty. -/
def reachersOfAll (back : Std.ExtTreeMap Digest (List Digest) compare) (newest : Array Digest) :
    Option DigestSet :=
  newest.foldl (init := none) fun acc m =>
    let here := reachersOf back m
    some (match acc with
      | none => here
      | some s => s.filter (here.contains ·))

/-- What `classify` needs about one author. -/
structure AuthorView where
  /-- The records the author's live records reach. -/
  reach : DigestSet
  /-- The digests the author's live records disown. -/
  disowned : DigestSet
  /-- The records that reach every live record of the author (see `reachersOfAll`). -/
  reachesAllLive : Option DigestSet

/-- For each author with a live record in the store: their `AuthorView`. Live digests that are
not stored are ignored. -/
def authorViews (c : CheckedStore) (live : Std.ExtTreeMap Digest (Array Digest) compare) :
    Std.ExtTreeMap Aci AuthorView compare :=
  let byAuthor : Std.ExtTreeMap Aci (Array Digest × DigestSet) compare :=
    live.foldl (init := ∅) fun m d dis =>
      match c.get d with
      | some r =>
        let (ls, ds) := m.getD r.author (#[], ∅)
        m.insert r.author (ls.push d, dis.foldl (fun s x => s.insert x) ds)
      | none => m
  let back := linkedBy c
  byAuthor.map fun _ (ls, ds) =>
    -- The author's live records that another of them reaches, through at least one link.
    let below := c.reachSet (ls.flatMap fun l => ((c.get l).map (·.links)).getD #[])
    let newest := ls.filter (!below.contains ·)
    ⟨c.reachSet ls, ds, reachersOfAll back newest⟩

/-- The status of the stored record `r` with digest `d`. `views` holds the author views and
`authors` the same as a list, sorted by author. -/
def status (views : Std.ExtTreeMap Aci AuthorView compare) (authors : List (Aci × AuthorView))
    (d : Digest) (r : Rec) : Status :=
  let heldOrUnconfirmed : Status :=
    match authors.find? (fun (a, v) => a != r.author && v.reach.contains d) with
    | some (a, _) => .heldBy a
    | none => .unconfirmed
  match views[r.author]? with
  | none => heldOrUnconfirmed
  | some v =>
    let reached := v.reach.contains d
    let disowned := v.disowned.contains d
    if reached && !disowned then .confirmedByAuthor
    else if disowned then .notConfirmedByAuthor
    else
      -- No live record of the author reaches `r`. If `r` does not reach one of them either, the
      -- two were written in parallel.
      match v.reachesAllLive with
      | some s => if s.contains d then heldOrUnconfirmed else .notConfirmedByAuthor
      | none => heldOrUnconfirmed

/-- `CLASSIFY`: the status of every stored record, keyed by digest. -/
def classify (c : CheckedStore) (facts : Array Fact) : Std.ExtTreeMap Digest Status compare :=
  let views := authorViews c (liveFacts facts)
  let authors := views.toList
  c.raw.map.map fun d r => status views authors d r

/-! ### `CLASSIFY` on a relative store

The same code over any raw store: a relative store's records, whose links may point to boundary
digests. `reachSet` and `get` simply skip a digest that is not stored. On a closed store it is
`classify` itself (`classify_raw`, by definition), so every theorem about `classify` covers the
closed stores `zrdtd` runs it on. -/

/-- `linkedBy` over a raw store. -/
def linkedByRaw (c : RawStore) : Std.ExtTreeMap Digest (List Digest) compare :=
  c.map.foldl (init := c.map.map fun _ _ => []) fun m d r =>
    r.links.foldl (init := m) fun m l => m.modify l (d :: ·)

/-- `authorViews` over a raw store. -/
def authorViewsRaw (c : RawStore) (live : Std.ExtTreeMap Digest (Array Digest) compare) :
    Std.ExtTreeMap Aci AuthorView compare :=
  let reach : Array Digest → DigestSet := fun ds => walk (fun r => r.links.toList) c.map ∅ ds.toList
  let byAuthor : Std.ExtTreeMap Aci (Array Digest × DigestSet) compare :=
    live.foldl (init := ∅) fun m d dis =>
      match c.map[d]? with
      | some r =>
        let (ls, ds) := m.getD r.author (#[], ∅)
        m.insert r.author (ls.push d, dis.foldl (fun s x => s.insert x) ds)
      | none => m
  let back := linkedByRaw c
  byAuthor.map fun _ (ls, ds) =>
    let below := reach (ls.flatMap fun l => ((c.map[l]?).map (·.links)).getD #[])
    let newest := ls.filter (!below.contains ·)
    ⟨reach ls, ds, reachersOfAll back newest⟩

/-- `classify` over a raw store: the status of every stored record, keyed by digest. -/
def classifyRaw (c : RawStore) (facts : Array Fact) : Std.ExtTreeMap Digest Status compare :=
  let views := authorViewsRaw c (liveFacts facts)
  let authors := views.toList
  c.map.map fun d r => status views authors d r

/-- On a closed store, `classifyRaw` is `classify`. -/
theorem classify_raw (c : CheckedStore) (facts : Array Fact) :
    classify c facts = classifyRaw c.raw facts := rfl

/-! ## A literal reference

`classifyRef` follows the rules of the module header word for word, record by record. It is slow
(it walks the links once per pair of records), and is here to check `classify` against
(`Zrdt.Examples` below, and a randomized comparison). -/

/-- Following links from the stored record `a` gets to `b` (`a` itself counts). -/
def reaches (c : CheckedStore) (a b : Digest) : Bool := (c.reachSet #[a]).contains b

/-- The smaller of two account ids, in byte order. -/
def minAci (a b : Aci) : Aci := if compare a b == .gt then b else a

/-- The status of record `r` with digest `d`, straight from the rules. `live` maps each live
digest to its disown list. -/
def statusRef (c : CheckedStore) (live : Std.ExtTreeMap Digest (Array Digest) compare)
    (d : Digest) (r : Rec) : Status :=
  -- The stored live records: digest, record, disown list.
  let lives := live.toList.filterMap fun (l, dis) => (c.get l).map fun x => (l, x, dis)
  let own := lives.filter fun (_, x, _) => x.author == r.author
  let reachedByAuthor := own.any fun (l, _, _) => reaches c l d
  let disowned := own.any fun (_, _, dis) => dis.contains d
  let parallel := own.any fun (l, _, _) => !reaches c l d && !reaches c d l
  if reachedByAuthor && !disowned then .confirmedByAuthor
  else if disowned || (parallel && !reachedByAuthor) then .notConfirmedByAuthor
  else
    let holders := lives.filterMap fun (l, x, _) =>
      if x.author != r.author && reaches c l d then some x.author else none
    match holders with
    | [] => .unconfirmed
    | a :: rest => .heldBy (rest.foldl minAci a)

/-- `classify`, computed literally from the rules (slow; for checking). -/
def classifyRef (c : CheckedStore) (facts : Array Fact) : Std.ExtTreeMap Digest Status compare :=
  let live := liveFacts facts
  c.raw.map.map fun d r => statusRef c live d r

/-! ## Example: restore from anyone (docs/PLAN.md §8, beat 5)

Dave imports Bob's export of the chat in `Zrdt.Store` (`a1`, `b1`, `c1`, `a2`). Someone appended
a fake `f1` in Bob's name on top of it. Then members write live. The statuses below are checked
when this file is built, and each one is compared with `classifyRef`. -/

namespace Examples

/-- A fake in Bob's name, on top of `a2`. Bob never wrote it. -/
def f1 : Rec := Rec.make group (dig 0xf1) #[hashRecord a2] bob

/-- Alice writes after `a2` (she never saw `f1`). -/
def a3 : Rec := Rec.make group (dig 0xa3) #[hashRecord a2] alice

/-- Bob writes after `a3` (he never saw `f1`). -/
def b2 : Rec := Rec.make group (dig 0xb2) #[hashRecord a3] bob

/-- Carol links the fake in a live message. -/
def c2 : Rec := Rec.make group (dig 0xc2) #[hashRecord f1] carol

/-- Bob writes after `b2` and `c2`, so his message now reaches the fake. -/
def b3 : Rec := Rec.make group (dig 0xb3) #[hashRecord b2, hashRecord c2] bob

/-- Names of all example records. -/
def namedAll : List (Rec × String) :=
  named ++ [(f1, "f1"), (a3, "a3"), (b2, "b2"), (c2, "c2"), (b3, "b3")]

/-- A status in words, with names for members. -/
def showStatus : Status → String
  | .confirmedByAuthor => "confirmed by author"
  | .notConfirmedByAuthor => "NOT confirmed by author"
  | .heldBy a => if a == alice then "held by alice" else if a == bob then "held by bob"
      else if a == carol then "held by carol" else "held by someone"
  | .unconfirmed => "unconfirmed"

/-- A live fact for a record, with an optional disown list. -/
def liveFact (r : Rec) (disown : Array Digest := #[]) : Fact := ⟨hashRecord r, .live, disown⟩

/-- Load the records, classify them, and list `name: status` sorted by name. -/
def classified (rs : Array Rec) (facts : Array Fact) : Array String :=
  let c := ((CheckedStore.empty group).acceptAll rs).1
  let nameOf (d : Digest) := ((namedAll.find? fun (r, _) => hashRecord r == d).map (·.2)).getD "?"
  ((classify c facts).toList.map fun (d, st) => s!"{nameOf d}: {showStatus st}").toArray.qsort
    (· < ·)

/-- Print `classified`, one record per line. -/
def printClassified (rs : Array Rec) (facts : Array Fact) : IO Unit :=
  for line in classified rs facts do IO.println line

/-- `classify` and `classifyRef` agree on these records and facts. -/
def agrees (rs : Array Rec) (facts : Array Fact) : Bool :=
  let c := ((CheckedStore.empty group).acceptAll rs).1
  (classify c facts).toList == (classifyRef c facts).toList

end Examples

open Examples

-- Imported, nobody has written live: everything is unconfirmed.
/--
info: a1: unconfirmed
a2: unconfirmed
b1: unconfirmed
c1: unconfirmed
f1: unconfirmed
-/
#guard_msgs in #eval printClassified #[a1, b1, c1, a2, f1] #[]

-- Alice writes `a3` live: her messages are confirmed, the replies are held by her. The fake is
-- still unconfirmed: no live message reaches it.
/--
info: a1: confirmed by author
a2: confirmed by author
a3: confirmed by author
b1: held by alice
c1: held by alice
f1: unconfirmed
-/
#guard_msgs in #eval printClassified #[a1, b1, c1, a2, f1, a3] #[liveFact a3]

-- Bob writes `b2` live. It reaches `b1` but not `f1`, and `f1` does not reach it: the fake is
-- "not confirmed by Bob".
/--
info: a1: confirmed by author
a2: confirmed by author
a3: confirmed by author
b1: confirmed by author
b2: confirmed by author
c1: held by alice
f1: NOT confirmed by author
-/
#guard_msgs in #eval printClassified #[a1, b1, c1, a2, f1, a3, b2] #[liveFact a3, liveFact b2]

-- Before Bob writes, Carol links the fake live: it is "held by carol".
/--
info: a1: confirmed by author
a2: confirmed by author
a3: confirmed by author
b1: held by alice
c1: confirmed by author
c2: confirmed by author
f1: held by carol
-/
#guard_msgs in #eval printClassified #[a1, b1, c1, a2, f1, a3, c2] #[liveFact a3, liveFact c2]

-- Bob's `b3` links Carol's `c2`, so it reaches the fake. Without a disown the fake would count as
-- Bob's (the limit `relay_attribution_indistinguishable`). Bob's app disowns it, and then it is
-- "not confirmed by Bob". Only `f1` is shown; every other record is confirmed by its author.
#guard (classified #[a1, b1, c1, a2, f1, a3, b2, c2, b3]
  #[liveFact a3, liveFact b2, liveFact c2, liveFact b3]).all (·.endsWith ": confirmed by author")
/-- info: f1: NOT confirmed by author -/
#guard_msgs in #eval
  let lines := classified #[a1, b1, c1, a2, f1, a3, b2, c2, b3]
    #[liveFact a3, liveFact b2, liveFact c2, liveFact b3 #[hashRecord f1]]
  IO.println ((lines.find? fun (l : String) => l.startsWith "f1").getD "?")

-- `linkedBy` (links followed backwards), `reachersOf`, `reachersOfAll`.
#guard let back := linkedBy all4
  back[hashRecord a1]?.map (·.length) == some 2 && back[hashRecord a2]? == some []
#guard let back := linkedBy all4
  (reachersOf back (hashRecord c1)).toList == [hashRecord c1, hashRecord a2]
#guard let back := linkedBy all4
  ((reachersOfAll back #[hashRecord b1, hashRecord c1]).map (·.toList)) == some [hashRecord a2]

-- `reaches` and `minAci`.
#guard reaches all4 (hashRecord a2) (hashRecord a1) && !reaches all4 (hashRecord a1) (hashRecord a2)
#guard minAci carol alice == alice && minAci alice bob == alice

-- `authorViews`: Alice's live `a2` reaches everything; nobody else has a live record.
#guard let v := authorViews all4 (liveFacts #[liveFact a2])
  v.size == 1 && (v[alice]?.map (·.reach.size)) == some 4

-- Relayed and imported records count for nothing here; only live ones do.
#guard classified #[a1, b1] #[⟨hashRecord b1, .relayed carol, #[]⟩] ==
  #["a1: unconfirmed", "b1: unconfirmed"]

-- The fast `classify` agrees with the literal `classifyRef` on every step above.
#guard agrees #[a1, b1, c1, a2, f1] #[]
#guard agrees #[a1, b1, c1, a2, f1, a3] #[liveFact a3]
#guard agrees #[a1, b1, c1, a2, f1, a3, b2] #[liveFact a3, liveFact b2]
#guard agrees #[a1, b1, c1, a2, f1, a3, c2] #[liveFact a3, liveFact c2]
#guard agrees #[a1, b1, c1, a2, f1, a3, b2, c2, b3]
  #[liveFact a3, liveFact b2, liveFact c2, liveFact b3 #[hashRecord f1]]

end Zrdt
