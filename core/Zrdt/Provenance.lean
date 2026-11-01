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

/-- What `classify` needs about one author: the digests of their live records in the store,
everything those records reach, and everything they disown. -/
structure AuthorView where
  /-- The author's live records in the store. -/
  live : Array Digest
  /-- The records the author's live records reach. -/
  reach : DigestSet
  /-- The digests the author's live records disown. -/
  disowned : DigestSet

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
  byAuthor.map fun _ (ls, ds) => ⟨ls, c.reachSet ls, ds⟩

/-- The status of the stored record `r` with digest `d`, given the author views (see the module
header for the rules and their order). -/
def status (c : CheckedStore) (views : Std.ExtTreeMap Aci AuthorView compare) (d : Digest)
    (r : Rec) : Status :=
  let heldOrUnconfirmed : Status :=
    match views.toList.find? (fun (a, v) => a != r.author && v.reach.contains d) with
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
      -- No live record of the author reaches `r`. Does `r` miss one of them too?
      let below := c.reachSet #[d]
      if v.live.any (fun l => !below.contains l) then .notConfirmedByAuthor
      else heldOrUnconfirmed

/-- `CLASSIFY`: the status of every stored record, keyed by digest. -/
def classify (c : CheckedStore) (facts : Array Fact) : Std.ExtTreeMap Digest Status compare :=
  let views := authorViews c (liveFacts facts)
  c.raw.map.map fun d r => status c views d r

end Zrdt
