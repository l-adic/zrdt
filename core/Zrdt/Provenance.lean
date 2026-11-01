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

end Zrdt
