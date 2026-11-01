/-
Copyright (c) 2026 zrdt contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: zrdt contributors
-/
import Zrdt.Store

/-!
# Proofs about the encodings, and about loading a store (docs/PLAN.md §3.2, §3.4)

This file imports only the shipped code (`zrdt-core`), not Mathlib. Its statements are about the
code alone, in the code's own terms. `Refine.lean` and `Api.lean` restate some of them over the
spec model.

**Encodings.**

- `encode_injective`: two different records never have the same bytes. No size bound is needed.
  Every field has a fixed size except the links, and each link has a fixed size, so `decode`
  takes any encoding apart again (`decode_encode`, in `Zrdt.Encode`).
- `hashRecord_collision`: two different records with the same digest are two different byte
  strings with the same SHA-256. So the only way two records collide is a SHA-256 collision.
- `encodeBlob_injective`: two well-sized blobs with the same bytes have the same chat and the same
  records in the same order.

**Loading a store** (`open`, `salvage`). `open` and `salvage` decode the blob, check that it is for
the requested chat, and then load its records (`openRecords`, `salvageRecords`), all through
`acceptAll` on an empty store.

- `open_eq_ok_iff`, `salvage_eq_ok_iff`: that split, as an equivalence.
- `openRecords_eq_ok_iff`: loading succeeds exactly when the records are within the size limits,
  all of the chat, never two different records under one digest (`NoCollision`), and can be
  listed in an accept order (`HasAcceptOrder`). The store then holds exactly those records.
  `open_iff_records` combines the two: this is `open_iff` of `Api.lean` in the code's terms.
- `acceptAll_closed`: after `acceptAll` on an empty store, every record of the batch whose links
  are all stored is itself stored (when the checks pass and no two records share a digest). So the
  result is closed under "accept one more record of the batch"; with the model's `buildRetry` this
  gives `salvage_spec`.
- `mem_acceptAll_left`: the records `acceptAll` leaves over are exactly the batch records it did
  not store.
- `salvageRecords_ok`: what a successful salvage returns: a store of records of the batch, closed
  as above, and `dropped` the digests of every batch record not stored.

**Stores.** `CheckedStore.eq_of_records`: two stores of the same chat with the same records are
equal. (The keys are the records' digests, and the heads are computed from the map.)
-/

namespace Zrdt

/-! ## Records -/

/-- **Different records have different encodings.** This holds for every record, with no size
bound: `decode` inverts `encode` (`decode_encode`). -/
theorem encode_injective : Function.Injective encode := by
  intro r s h
  have hr := decode_encode r
  rw [h, decode_encode s] at hr
  exact (Option.some.inj hr).symm

example : encode Examples.first ≠ encode Examples.reply :=
  fun h => by have := encode_injective h; revert this; decide

/-- **A record collision is a SHA-256 collision.** Two different records with the same digest
have two different encodings with the same SHA-256. -/
theorem hashRecord_collision {r s : Rec} (hne : r ≠ s) (h : hashRecord r = hashRecord s) :
    encode r ≠ encode s ∧ sha256 (encode r) = sha256 (encode s) :=
  ⟨fun he => hne (encode_injective he), h⟩

/-- Two records have the same digest exactly when their encodings have the same SHA-256. -/
theorem hashRecord_eq_iff {r s : Rec} :
    hashRecord r = hashRecord s ↔ sha256 (encode r) = sha256 (encode s) := Iff.rfl

/-! ## Store blobs -/

/-- Two well-sized blobs with the same bytes were written for the same chat and the same records,
in the same order. -/
theorem encodeBlob_injective {g g' : GroupId} {u u' : Array Rec} (hu : WellSized u)
    (hu' : WellSized u') (h : encodeBlob g u = encodeBlob g' u') : g = g' ∧ u = u' := by
  have h1 := decodeBlob_encodeBlob g u hu
  rw [h, decodeBlob_encodeBlob g' u' hu'] at h1
  simp only [Option.some.injEq, Prod.mk.injEq] at h1
  exact ⟨h1.1.symm, h1.2.symm⟩

open Examples in
example : encodeBlob group #[first] ≠ encodeBlob otherGroup #[first] := by
  intro h
  have := (encodeBlob_injective (by decide +kernel) (by decide +kernel) h).1
  revert this; decide

/-! ## Conditions on a list of records -/

/-- `NoCollision u`: no two different records of `u` have the same digest. (The same record
twice is allowed.) -/
def NoCollision (u : Array Rec) : Prop :=
  ∀ x ∈ u, ∀ y ∈ u, hashRecord x = hashRecord y → x = y

open Examples in
example : NoCollision #[first, first] := by
  intro x hx y hy _
  simp only [List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false, or_self] at hx hy
  rw [hx, hy]

/-- `HasAcceptOrder u`: the records of `u` (and no others) can be listed in an accept order, so
that each record's links are digests of records listed after it (`AcceptOrder`, newest first).
Accepting the list from the end, every record's links are present when it arrives. -/
def HasAcceptOrder (u : Array Rec) : Prop :=
  ∃ l, AcceptOrder l ∧ ∀ r, r ∈ l ↔ r ∈ u

open Examples in
example : HasAcceptOrder #[first] :=
  ⟨[first], .cons (by simp [first, Rec.make, canonicalLinks]) .nil, by simp⟩

namespace CheckedStore

/-! ## Stores are determined by their chat and records -/

/-- A stored record is stored under its own digest. -/
theorem getElem?_eq_some_iff {c : CheckedStore} {k : Digest} {x : Rec} :
    c.raw.map[k]? = some x ↔ x ∈ c.records ∧ hashRecord x = k :=
  ⟨fun h => ⟨mem_records.mpr ⟨k, h⟩, c.built.hash_eq k x h⟩, fun ⟨h, hk⟩ => by
    obtain ⟨k', hk'⟩ := mem_records.mp h
    rw [← hk, c.built.hash_eq k' x hk']; exact hk'⟩

/-- A record is in the store exactly when it is stored under its digest. -/
theorem mem_records_iff {c : CheckedStore} {x : Rec} :
    x ∈ c.records ↔ c.raw.map[hashRecord x]? = some x := by
  rw [getElem?_eq_some_iff]; simp

/-- A digest is a key of the store exactly when it is the digest of a stored record. -/
theorem mem_map_iff {c : CheckedStore} {d : Digest} :
    d ∈ c.raw.map ↔ ∃ x ∈ c.records, hashRecord x = d := by
  rw [Std.ExtTreeMap.mem_iff_isSome_getElem?, Option.isSome_iff_exists]
  simp only [getElem?_eq_some_iff]

/-- **Two stores of the same chat with the same records are equal.** The keys are the records'
digests, and the heads are the keys no record links, so the records fix everything. -/
theorem eq_of_records {c d : CheckedStore} (hg : c.group = d.group)
    (hr : ∀ x, x ∈ c.records ↔ x ∈ d.records) : c = d := by
  have hmap : c.raw.map = d.raw.map := by
    apply Std.ExtTreeMap.ext_getElem?
    intro k
    apply Option.ext
    intro x
    rw [getElem?_eq_some_iff, getElem?_eq_some_iff, hr]
  have hheads : c.raw.heads = d.raw.heads := by
    apply Std.ExtTreeSet.ext_mem
    intro dg
    rw [c.built.heads_iff, d.built.heads_iff, hmap]
  apply ext
  have hg' : c.raw.group = d.raw.group := hg
  revert hg' hmap hheads
  cases c.raw; cases d.raw
  intro hg hm hh
  simp only at hg hm hh
  rw [hg, hm, hh]

example (c : CheckedStore) : c = c := eq_of_records rfl fun _ => Iff.rfl

/-! ## `accept` and `acceptAll` -/

/-- A record already stored is accepted again, and nothing changes. -/
theorem accept_of_stored {c : CheckedStore} {x : Rec} (h : x ∈ c.records) :
    (c.accept x).1 = .accepted (hashRecord x) := by
  have hx := mem_records_iff.mp h
  rw [accept_fst]
  apply rawAccept_of_ok (c.built.group_eq _ x hx) (c.built.wellSized _ x hx)
    (c.built.closed _ x hx)
  · intro old hold; rw [hx] at hold; exact (Option.some.inj hold).symm
  · intro hn
    exact absurd (Std.ExtTreeMap.mem_iff_isSome_getElem?.mpr (by simp [hx])) hn

/-- **The records `acceptAll` leaves over** are exactly the records of the batch that it did not
store. -/
theorem mem_acceptAll_left {c : CheckedStore} {rs : Array Rec} {x : Rec} :
    x ∈ (c.acceptAll rs).2 ↔ x ∈ rs ∧ x ∉ (c.acceptAll rs).1.records := by
  obtain ⟨_, _, _, hstored, hsub⟩ := acceptAll_sound c rs
  have hstuck := acceptAll_stuck c rs
  constructor
  · intro hx
    exact ⟨hsub x hx, fun hs => hstuck x hx _ (accept_of_stored hs)⟩
  · rintro ⟨hx, hn⟩
    exact Classical.byContradiction fun hl => hn (mem_records_iff.mpr (hstored x hx hl))

/-- What `acceptAll` on an empty store of chat `g` stores comes from the batch, and is of
chat `g`. -/
theorem acceptAll_empty_records {g : GroupId} {u : Array Rec} :
    ((empty g).acceptAll u).1.group = g ∧ ∀ x ∈ ((empty g).acceptAll u).1.records, x ∈ u := by
  obtain ⟨hg, _, honly, _, _⟩ := acceptAll_sound (empty g) u
  refine ⟨hg, fun x hx => ?_⟩
  obtain ⟨k, hk⟩ := mem_records.mp hx
  exact (honly k x hk).resolve_left (by simp [empty])

/-- **`acceptAll` stops only when stuck.** Load a batch `u` of chat `g` into an empty store, with
the batch within the size limits and no two different records sharing a digest. Then every
record of the batch whose links are all digests of stored records is stored itself. -/
theorem acceptAll_closed {g : GroupId} {u : Array Rec} (hw : WellSized u)
    (hg : ∀ r ∈ u, r.group = g) (hcol : NoCollision u) :
    ∀ r ∈ u, (∀ d ∈ r.links, ∃ x ∈ ((empty g).acceptAll u).1.records, hashRecord x = d) →
      r ∈ ((empty g).acceptAll u).1.records := by
  obtain ⟨hgrp, honly⟩ := acceptAll_empty_records (g := g) (u := u)
  have hleft := @mem_acceptAll_left (empty g) u
  have hstuck := acceptAll_stuck (empty g) u
  generalize (empty g).acceptAll u = res at hgrp honly hleft hstuck ⊢
  obtain ⟨e, left⟩ := res
  dsimp only at hgrp honly hleft hstuck ⊢
  intro x hx hl
  refine Classical.byContradiction fun hn => ?_
  apply hstuck x ((hleft (x := x)).mpr ⟨hx, hn⟩) (hashRecord x)
  rw [accept_fst]
  apply rawAccept_of_ok ((hg x hx).trans hgrp.symm) (hw.2 x hx)
    (fun d hd => mem_map_iff.mpr (hl d hd))
  · intro old hold
    obtain ⟨hold, hh⟩ := getElem?_eq_some_iff.mp hold
    exact hcol old (honly old hold) x hx hh
  · intro hk
    have := size_lt_of_keys (m := e.raw.map) (u := u) (r := x) (fun k hk => by
      obtain ⟨y, hy, rfl⟩ := mem_map_iff.mp hk
      exact ⟨y, honly y hy, rfl⟩) hx hk
    have := hw.1
    omega

/-! ## `open` -/

/-- The checks `open` and `salvage` make first pass exactly when the records are within the size
limits and all of chat `g`. -/
theorem checkInput_eq_none_iff {g : GroupId} {u : Array Rec} :
    checkInput g u = none ↔ WellSized u ∧ ∀ r ∈ u, r.group = g := by
  unfold checkInput
  by_cases hw : WellSized u
  · simp only [hw, ↓reduceIte, true_and]
    split
    · rename_i ha
      simp only [allInChat, Array.all_eq_true_iff_forall_mem, beq_iff_eq] at ha
      simpa using ha
    · rename_i ha
      simp only [allInChat, Array.all_eq_true_iff_forall_mem, beq_iff_eq] at ha
      simpa using ha
  · simp [hw]

/-- **`open` splits into decoding and loading.** It succeeds exactly when the blob decodes, its
chat is `g`, and its records load as a store of chat `g`. -/
theorem open_eq_ok_iff {g : GroupId} {b : ByteArray} {c : CheckedStore} :
    CheckedStore.open g b = .ok c ↔ ∃ u, decodeBlob b = some (g, u) ∧ openRecords g u = .ok c := by
  unfold CheckedStore.open
  split
  · rename_i h
    simp [h]
  · rename_i g' u h
    simp only [h, Option.some.injEq, Prod.mk.injEq]
    split
    · rename_i hne
      simp only [reduceCtorEq, false_iff, not_exists, not_and]
      intro _ h1
      exact absurd h1.1 hne
    · rename_i heq
      simp only [Decidable.not_not] at heq
      subst heq
      constructor
      · intro ho; exact ⟨u, ⟨rfl, rfl⟩, ho⟩
      · rintro ⟨u', ⟨_, rfl⟩, ho⟩; exact ho

/-- **When loading records succeeds.** `openRecords g u` returns the store `c` exactly when the
records are within the size limits, all of chat `g`, never two different records under one
digest, and can be listed in an accept order; and `c` is then the store of chat `g` holding
exactly the records of `u`. -/
theorem openRecords_eq_ok_iff {g : GroupId} {u : Array Rec} {c : CheckedStore} :
    openRecords g u = .ok c ↔
      WellSized u ∧ (∀ r ∈ u, r.group = g) ∧ NoCollision u ∧ HasAcceptOrder u ∧
        c.group = g ∧ ∀ x, x ∈ c.records ↔ x ∈ u := by
  constructor
  · intro h
    obtain ⟨hg, hw, hchat, hmap⟩ := openRecords_ok h
    have hrec : ∀ x, x ∈ c.records ↔ x ∈ u := fun x => by
      rw [mem_records_iff, hmap]; simp
    refine ⟨hw, hchat, ?_, ?_, hg, hrec⟩
    · intro x hx y hy hxy
      have h1 := (hmap (hashRecord x) x).mpr ⟨hx, rfl⟩
      have h2 := (hmap (hashRecord x) y).mpr ⟨hy, hxy.symm⟩
      rw [h1] at h2
      exact Option.some.inj h2
    · obtain ⟨l, hl, hmem⟩ := c.built.order
      exact ⟨l, hl, fun r => (hmem r).trans (mem_records.symm.trans (hrec r))⟩
  · rintro ⟨hw, hchat, hcol, hord, hg, hrec⟩
    obtain ⟨e, he⟩ := openRecords_complete hw hchat hcol hord
    obtain ⟨heg, _, _, hmap⟩ := openRecords_ok he
    have : e = c := by
      apply eq_of_records (heg.trans hg.symm)
      intro x
      rw [hrec, mem_records_iff, hmap]
      simp
    rw [he, this]

/-- **Loading succeeds when `acceptAll` stores every record.** If the checks pass and every
record of `u` is stored by `acceptAll` on an empty store of chat `g`, then `openRecords` returns
that store. (With `acceptAll_closed`, this is how the model's `AcceptBuilt` gives a successful
`open`: `AcceptBuilt` means `buildRetry` keeps everything, and `acceptAll` keeps at least what
`buildRetry` keeps.) -/
theorem openRecords_eq_ok_of_stored {g : GroupId} {u : Array Rec} (hw : WellSized u)
    (hg : ∀ r ∈ u, r.group = g) (hall : ∀ r ∈ u, r ∈ ((empty g).acceptAll u).1.records) :
    openRecords g u = .ok ((empty g).acceptAll u).1 := by
  have hcheck : checkInput g u = none := checkInput_eq_none_iff.mpr ⟨hw, hg⟩
  have hleft : ((empty g).acceptAll u).2 = #[] := by
    rw [Array.eq_empty_iff_forall_not_mem]
    intro x hx
    have := mem_acceptAll_left.mp hx
    exact this.2 (hall x this.1)
  unfold openRecords
  rw [hcheck]
  dsimp only
  rw [hleft]
  rfl

/-- **`open` in the code's terms** (`open_iff` of `Api.lean` before the bridge to the model):
`open g b` returns `c` exactly when `b` decodes to chat `g` and records `u` that are within the
size limits, all of chat `g`, free of collisions and listable in an accept order, and `c` is the
store of chat `g` holding exactly the records of `u`. -/
theorem open_iff_records {g : GroupId} {b : ByteArray} {c : CheckedStore} :
    CheckedStore.open g b = .ok c ↔
      ∃ u, decodeBlob b = some (g, u) ∧ WellSized u ∧ (∀ r ∈ u, r.group = g) ∧
        NoCollision u ∧ HasAcceptOrder u ∧ c.group = g ∧ ∀ x, x ∈ c.records ↔ x ∈ u := by
  rw [open_eq_ok_iff]
  simp only [openRecords_eq_ok_iff]

/-- A store's own blob satisfies every condition of `open_iff_records` (the hypotheses are
satisfiable). -/
example (c : CheckedStore) : ∃ u, decodeBlob c.encode = some (c.group, u) ∧ WellSized u ∧
    (∀ r ∈ u, r.group = c.group) ∧ NoCollision u ∧ HasAcceptOrder u ∧ c.group = c.group ∧
    ∀ x, x ∈ c.records ↔ x ∈ u :=
  open_iff_records.mp (encode_reopens c)

/-- The spec rejects a bad input: a record whose link points to nothing has no accept order. -/
private theorem not_hasAcceptOrder_b1 : ¬ HasAcceptOrder #[Examples.b1] := by
  rintro ⟨l, hl, hmem⟩
  have hb : Examples.b1 ∈ l := (hmem _).mpr (by simp)
  obtain ⟨r', hr', he⟩ := hl.links _ hb (hashRecord Examples.a1) (by simp [Examples.b1])
  have : r' = Examples.b1 := by simpa using (hmem r').mp hr'
  subst this
  revert he
  decide +kernel

/-- So a blob holding only `b1` (its link `a1` cut out) does not open, as any store. -/
example (c : CheckedStore) :
    CheckedStore.open Examples.group (encodeBlob Examples.group #[Examples.b1]) ≠ .ok c := by
  intro h
  obtain ⟨u, hu, -, -, -, hord, -⟩ := open_iff_records.mp h
  rw [decodeBlob_encodeBlob _ _ (by decide +kernel)] at hu
  cases hu
  exact not_hasAcceptOrder_b1 hord

/-! ## `salvage` -/

/-- **`salvage` splits into decoding and loading**, like `open`. -/
theorem salvage_eq_ok_iff {g : GroupId} {b : ByteArray} {s : Salvaged} :
    salvage g b = .ok s ↔ ∃ u, decodeBlob b = some (g, u) ∧ salvageRecords g u = .ok s := by
  unfold salvage
  split
  · rename_i h
    simp [h]
  · rename_i g' u h
    simp only [h, Option.some.injEq, Prod.mk.injEq]
    split
    · rename_i hne
      simp only [reduceCtorEq, false_iff, not_exists, not_and]
      intro _ h1
      exact absurd h1.1 hne
    · rename_i heq
      simp only [Decidable.not_not] at heq
      subst heq
      constructor
      · intro ho; exact ⟨u, ⟨rfl, rfl⟩, ho⟩
      · rintro ⟨u', ⟨_, rfl⟩, ho⟩; exact ho

/-- The digests the fold in `leftoverReport` collects: those of the given entries. -/
theorem mem_fold_insert (l : List (Digest × Rec)) (s : DigestSet) (d : Digest) :
    d ∈ l.foldl (fun s (p : Digest × Rec) => s.insert p.1) s ↔ d ∈ s ∨ ∃ p ∈ l, p.1 = d := by
  induction l generalizing s with
  | nil => simp
  | cons p ps ih =>
    simp only [List.foldl_cons, ih, Std.ExtTreeSet.mem_insert, Std.LawfulEqCmp.compare_eq_iff_eq,
      List.mem_cons, exists_eq_or_imp]
    rw [or_comm (a := p.fst = d), or_assoc]

/-- The `dropped` list of `leftoverReport`: the digests of the given entries. -/
theorem mem_leftoverReport_fst {c : CheckedStore} {left : Array (Digest × Rec)} {d : Digest} :
    d ∈ (leftoverReport c left).1 ↔ ∃ p ∈ left, p.1 = d := by
  simp only [leftoverReport, List.mem_toArray, Std.ExtTreeSet.mem_toList]
  rw [← Array.foldl_toList]
  rw [mem_fold_insert]
  simp

/-- The `dropped` list of `leftoverReport` is sorted, with no digest twice. -/
theorem leftoverReport_fst_sorted {c : CheckedStore} {left : Array (Digest × Rec)} :
    StrictlySorted (leftoverReport c left).1 := by
  unfold StrictlySorted leftoverReport
  exact Std.ExtTreeSet.ordered_toList

/-- **What a successful salvage returns.** The input was within the size limits and all of
chat `g`. The store is of chat `g` and holds only records of `u`. If no two different records of
`u` share a digest, the store is closed: every record of `u` whose links are all digests of
stored records is stored. And `dropped` is sorted and holds exactly the digests of the records
of `u` that were not stored. -/
theorem salvageRecords_ok {g : GroupId} {u : Array Rec} {s : Salvaged}
    (h : salvageRecords g u = .ok s) :
    WellSized u ∧ (∀ r ∈ u, r.group = g) ∧ s.store.group = g ∧
      (∀ x ∈ s.store.records, x ∈ u) ∧
      (NoCollision u → ∀ r ∈ u, (∀ d ∈ r.links, ∃ x ∈ s.store.records, hashRecord x = d) →
        r ∈ s.store.records) ∧
      (∀ d, d ∈ s.dropped ↔ ∃ r ∈ u, r ∉ s.store.records ∧ hashRecord r = d) ∧
      StrictlySorted s.dropped := by
  unfold salvageRecords at h
  split at h
  · simp at h
  rename_i hcheck
  obtain ⟨hw, hchat⟩ := checkInput_eq_none_iff.mp hcheck
  have hclosed := acceptAll_closed hw hchat
  obtain ⟨hgrp, honly⟩ := acceptAll_empty_records (g := g) (u := u)
  have hleft := @mem_acceptAll_left (empty g) u
  generalize (empty g).acceptAll u = res at h hclosed hgrp honly hleft
  obtain ⟨e, left⟩ := res
  dsimp only at h hclosed hgrp honly hleft
  split at h
  · simp at h
  simp only [Except.ok.injEq] at h
  subst h
  refine ⟨hw, hchat, hgrp, honly, hclosed, fun d => ?_, leftoverReport_fst_sorted (c := e)⟩
  dsimp only
  rw [mem_leftoverReport_fst]
  simp only [withDigests, Array.mem_map, hleft]
  constructor
  · rintro ⟨_, ⟨r, hr, rfl⟩, rfl⟩
    exact ⟨r, hr.1, hr.2, rfl⟩
  · rintro ⟨r, hr, hn, rfl⟩
    exact ⟨_, ⟨r, ⟨hr, hn⟩, rfl⟩, rfl⟩

end CheckedStore

end Zrdt
