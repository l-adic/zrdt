/-
Copyright (c) 2026 zrdt contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: zrdt contributors
-/
import Crdt.Merkle.Bridge
import Crdt.Merkle.Refine
import Crdt.Merkle.ClassifyStatus
import Crdt.Merkle.Rel
import Zrdt.Serve

/-!
# The challenge for `lake comparator` (docs/PLAN.md §3.2)

The advertised statements of `Crdt/Merkle/Api.lean`, and `Zrdt.encode_injective`
(`Crdt/Merkle/EncodeProofs.lean`), stated again here word for word, each with `sorry` as its
proof. `lake comparator` (config: `comparator.json`) checks that the solution module
(`Crdt.Merkle.Api`) proves each of these names with exactly this statement, that its proof uses
no axiom other than `propext`, `Classical.choice` and `Quot.sound`, and that the kernel accepts
it.

This file imports only the modules that define what the statements mention (`Bridge.lean`,
`Refine.lean`, `ClassifyStatus.lean`, `Rel.lean`, `core/Zrdt/Serve.lean`, and through them the
spec and the shipped code). It must not import `Api.lean`, `EncodeProofs.lean`, `LoadApi.lean`
or `ServeAbs.lean`: those declare the names below or import a module that does.

Keep this file in step with `Api.lean` and with the list in `comparator.json` and
`Test/Axioms.lean`. It is not a default target, so `lake build` never sees its `sorry`s.
-/

namespace Zrdt

open Crdt.Merkle

theorem CheckedStore.no_collision (c : CheckedStore) : ¬ CollisionIn hashSpec (abs c) :=
  sorry

theorem CheckedStore.fetched (c : CheckedStore) :
    Fetched hashSpec (abs c) (Crdt.Merkle.heads hashSpec (abs c)) :=
  sorry

theorem CheckedStore.agree (c d : CheckedStore) (h : c.heads = d.heads) :
    abs c = abs d ∨ CollisionIn hashSpec (abs c ∪ abs d) :=
  sorry

theorem CheckedStore.abs_accept (c : CheckedStore) (r : Rec) : AcceptMeans c r (c.accept r) :=
  sorry

theorem CheckedStore.abs_merge {c d e : CheckedStore} (h : c.merge d = .ok e) :
    abs e = abs c ∪ abs d :=
  sorry

theorem CheckedStore.open_iff {g : GroupId} {b : ByteArray} {c : CheckedStore} :
    CheckedStore.open g b = .ok c ↔
      ∃ u, decodeBlob b = some (g, u) ∧ WellSized u ∧ AcceptBuilt hashSpec (specOf u) ∧
        ¬ CollisionIn hashSpec (specOf u) ∧ (∀ r ∈ u, r.group = g) ∧ abs c = specOf u ∧
        c.group = g :=
  sorry

theorem CheckedStore.salvage_spec {g : GroupId} {b : ByteArray} {s : Salvaged} {u : Array Rec}
    (h : salvage g b = .ok s) (hu : decodeBlob b = some (g, u)) :
    ¬ CollisionIn hashSpec (specOf u) ∧
      abs s.store = buildRetry hashSpec (specOf u) ∧ s.store.group = g ∧
      (∀ d, d ∈ s.dropped ↔ d ∈ digests hashSpec (specOf u \ buildRetry hashSpec (specOf u))) ∧
      StrictlySorted s.dropped :=
  sorry

theorem CheckedStore.encode_open (c : CheckedStore) :
    CheckedStore.open c.group c.encode = .ok c :=
  sorry

theorem CheckedStore.confirmed (c d : CheckedStore) (hs : Array Digest)
    (hc : ∀ h ∈ hs, c.has h = true) (hd : ∀ h ∈ hs, d.has h = true) :
    c.reachSet hs = d.reachSet hs ∨ CollisionIn hashSpec (abs c ∪ abs d) :=
  sorry

theorem CheckedStore.classify_spec (c : CheckedStore) (facts : Array Fact) (d : Digest)
    (st : Zrdt.Status) :
    (classify c facts)[d]? = some st ↔
      ∃ r, c.get d = some r ∧
        Crdt.Merkle.status hashSpec (abs c) (liveOf facts) (toSpec r) = st.toSpec :=
  sorry

theorem encode_injective : Function.Injective encode :=
  sorry

theorem CheckedStore.agree_rel (c : CheckedStore) (BS : Finset Digest) {F : SpecStore}
    {B : Finset Digest} (hh : headsRel hashSpec F B = headsRel hashSpec (abs c) BS)
    (hFB : ∀ r ∈ F, hashSpec r ∈ BS → hashSpec r ∈ digests hashSpec (abs c)) :
    ∀ d, Reach hashSpec F (headsRel hashSpec F B) d →
      (d ∈ digests hashSpec (abs c) ∧ ∀ r ∈ F, hashSpec r = d → r ∈ abs c) ∨
        (d ∈ BS ∧ d ∉ digests hashSpec (abs c) ∧ ∀ r ∈ F, hashSpec r ≠ d) ∨
        CollisionIn hashSpec (abs c ∪ F) :=
  sorry

theorem CheckedStore.serve_content (c : CheckedStore) {me : Serve.Me} {held : Serve.HeldMap}
    {q : Serve.Query} {r : Rec} {op : ByteArray} {ac : Bool}
    (he : Serve.Entry.addressed r (some op) ac ∈ Serve.serve c.raw me held q) :
    toSpec r ∈ abs c ∧ openingMatches r.group r.author r.commit op = true ∧
      ∃ aud, Serve.audienceOf op = some aud ∧ Serve.seats aud q.aci q.key = true :=
  sorry

theorem CheckedStore.serve_content_complete (c : CheckedStore) {me : Serve.Me}
    {held : Serve.HeldMap} {q : Serve.Query} {r : Rec} {op : ByteArray}
    (hr : toSpec r ∈ abs c) (hop : (held.getD (hashRecord r) {}).opening = some op)
    (hs : Serve.serveOpening me q (hashRecord r) r op = true)
    (hmode : (q.wanted = none ∧
        ¬ Reach hashSpec (abs c) (q.since ++ q.ownSince).toList.toFinset (hashRecord r)) ∨
      ∃ ws, q.wanted = some ws ∧ hashRecord r ∈ ws) :
    Serve.Entry.addressed r (some op) (Serve.authorCopy me (hashRecord r) r) ∈
      Serve.serve c.raw me held q :=
  sorry

end Zrdt
