/-
Copyright (c) 2026 zrdt contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: zrdt contributors
-/
import Crdt.Merkle.Bridge
import Crdt.Merkle.Refine
import Crdt.Merkle.ClassifyStatus

/-!
# The challenge for `lake comparator` (docs/PLAN.md §3.2)

The advertised statements of `Crdt/Merkle/Api.lean`, and `Zrdt.encode_injective`
(`Crdt/Merkle/EncodeProofs.lean`), stated again here word for word, each with `sorry` as its
proof. `lake comparator` (config: `comparator.json`) checks that the solution module
(`Crdt.Merkle.Api`) proves each of these names with exactly this statement, that its proof uses
no axiom other than `propext`, `Classical.choice` and `Quot.sound`, and that the kernel accepts
it.

This file imports only the modules that define what the statements mention (`Bridge.lean`,
`Refine.lean`, `ClassifyStatus.lean`, and through them the spec and the shipped code). It must
not import `Api.lean`, `EncodeProofs.lean` or `LoadApi.lean`: those declare the names below.

Keep this file in step with `Api.lean` and with the list in `comparator.json` and
`Test/Axioms.lean`. It is not a default target, so `lake build` never sees its `sorry`s.
## Where each statement appears in the presentation

The talk names three guarantees (G1–G3) and three laws of sync (L1–L3). The comment above each
statement gives its label, the plain-words line from the slides, and the demo beat it backs.

* **G1** You can confirm you see the same chat: `CheckedStore.agree` (with `no_collision` and
  `encode_injective` underneath).
* **G2** If a message is kept from you, you find out: `CheckedStore.abs_accept`,
  `CheckedStore.fetched`.
* **G3** A reply shows what its author had: `CheckedStore.confirmed`, `CheckedStore.classify_spec`.
* **L1** Members restore each other's history: `CheckedStore.open_iff`, `CheckedStore.salvage_spec`,
  `CheckedStore.abs_merge`, `CheckedStore.encode_open`.
* **L2** Nobody can quietly withhold what you're owed: in this build, through **G1** (a member
  with a message you lack has a different code). The reply rule (`serve_content_complete`) is
  in the next version (branch `join`), not in this challenge.
* **L3** Join late, check against a member: next version only (`newcomer_agree'`, branch `join`).
  The next-version statements for L1's reply rule (`serve_content`), L2 and L3 are not in this
  challenge.

The limit on the slides, "the newest message is invisible until a later one names it, or you
compare", is `withheld_tail_undetectable` in `Crdt/Merkle/Chat.lean`. It is proved, but it is not
a challenge statement.
-/

namespace Zrdt

open Crdt.Merkle

-- G1 (underneath): no two different messages in one chat share a fingerprint.
-- The 'or two share a fingerprint' fallback of G1 and G3 cannot happen inside one store.
theorem CheckedStore.no_collision (c : CheckedStore) : ¬ CollisionIn hashSpec (abs c) :=
  sorry

-- G2: your chat holds every message its newest messages point back to, and nothing else.
-- So a message that a later one names, and you lack, shows as a hole with a name. Beat 2.
theorem CheckedStore.fetched (c : CheckedStore) :
    Fetched hashSpec (abs c) (Crdt.Merkle.heads hashSpec (abs c)) :=
  sorry

-- G1, You can confirm you see the same chat: same code, exactly the same messages, or two
-- different messages share a fingerprint. Beats 1 and 3 (the compare code); also L2 in this build.
theorem CheckedStore.agree (c d : CheckedStore) (h : c.heads = d.heads) :
    abs c = abs d ∨ CollisionIn hashSpec (abs c ∪ abs d) :=
  sorry

-- G2, If a message is kept from you, you find out: a message is added only if everything
-- it names is there; otherwise the app is told exactly what is missing. Beat 2.
theorem CheckedStore.abs_accept (c : CheckedStore) (r : Rec) : AcceptMeans c r (c.accept r) :=
  sorry

-- L1, Members restore each other's history: catching up from another copy keeps both sets
-- of messages.
theorem CheckedStore.abs_merge {c d e : CheckedStore} (h : c.merge d = .ok e) :
    abs e = abs c ∪ abs d :=
  sorry

-- L1: a copy loads only if every link in it finds its target. Beat 4 (the doctored backup
-- is refused and the missing message named).
theorem CheckedStore.open_iff {g : GroupId} {b : ByteArray} {c : CheckedStore} :
    CheckedStore.open g b = .ok c ↔
      ∃ u, decodeBlob b = some (g, u) ∧ WellSized u ∧ AcceptBuilt hashSpec (specOf u) ∧
        ¬ CollisionIn hashSpec (specOf u) ∧ (∀ r ∈ u, r.group = g) ∧ abs c = specOf u ∧
        c.group = g :=
  sorry

-- L1: "Keep what verifies" keeps exactly what checks out, the most any app could. Beat 4.
theorem CheckedStore.salvage_spec {g : GroupId} {b : ByteArray} {s : Salvaged} {u : Array Rec}
    (h : salvage g b = .ok s) (hu : decodeBlob b = some (g, u)) :
    ¬ CollisionIn hashSpec (specOf u) ∧
      abs s.store = buildRetry hashSpec (specOf u) ∧ s.store.group = g ∧
      (∀ d, d ∈ s.dropped ↔ d ∈ digests hashSpec (specOf u \ buildRetry hashSpec (specOf u))) ∧
      StrictlySorted s.dropped :=
  sorry

-- L1: saving and reopening gives back exactly the same chat, so an honest app's own copy
-- always restores.
theorem CheckedStore.encode_open (c : CheckedStore) :
    CheckedStore.open c.group c.encode = .ok c :=
  sorry

-- G3, A reply shows what its author had: a member's new message confirms exactly what is
-- behind it (that they hold it, not who wrote it). Beat 5.
theorem CheckedStore.confirmed (c d : CheckedStore) (hs : Array Digest)
    (hc : ∀ h ∈ hs, c.has h = true) (hd : ∀ h ∈ hs, d.has h = true) :
    c.reachSet hs = d.reachSet hs ∨ CollisionIn hashSpec (abs c ∪ abs d) :=
  sorry

-- G3: every label ("confirmed by", "held by", "not confirmed by", "unconfirmed") is exactly
-- as specified. Beat 5 (the two fakes become "not confirmed by Bob").
theorem CheckedStore.classify_spec (c : CheckedStore) (facts : Array Fact) (d : Digest)
    (st : Zrdt.Status) :
    (classify c facts)[d]? = some st ↔
      ∃ r, c.get d = some r ∧
        Crdt.Merkle.status hashSpec (abs c) (liveOf facts) (toSpec r) = st.toSpec :=
  sorry

-- G1 and G2 (underneath): different messages are never written as the same bytes, so the
-- fingerprint of the bytes is a fingerprint of the message.
theorem encode_injective : Function.Injective encode :=
  sorry

end Zrdt
