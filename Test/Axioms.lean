/-
Copyright (c) 2026 crdt-lean contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: crdt-lean contributors
-/
import Crdt
import Zrdt.Proto
import Zrdt.Serve
import Zrdt.ChatStore

/-!
# Axiom footprint gate

Every headline theorem below is pinned to the clean baseline
`{propext, Classical.choice, Quot.sound}` (or fewer) via `#guard_msgs`, which
fails elaboration on ANY drift — a new axiom, `sorry` (`sorryAx`), or
`native_decide` (`Lean.ofReduceBool` / `Lean.trustCompiler`).

This module is a `defaultTarget`, so a plain `lake build` elaborates it and the
gate cannot silently fail to run. Scope: the CvRDT merge algebra core and the
G-Counter convergence headlines (from crdt-lean), and, for zrdt, exactly the
`Api.lean` statements of docs/PLAN.md §3.2 and docs/JOIN_PLAN.md §7.3 plus
`Zrdt.encode_injective`, and the proof obligations listed below.
Extending the gate to the OR-Set / Sequence modules is a follow-up.
-/

-- Merge algebra core (`Crdt.Defs`).

/-- info: 'Crdt.merge_comm' depends on axioms: [propext] -/
#guard_msgs in #print axioms Crdt.merge_comm

/-- info: 'Crdt.merge_assoc' depends on axioms: [propext] -/
#guard_msgs in #print axioms Crdt.merge_assoc

/-- info: 'Crdt.merge_idem' depends on axioms: [propext] -/
#guard_msgs in #print axioms Crdt.merge_idem

/-- info: 'Crdt.merge_bot' depends on axioms: [propext] -/
#guard_msgs in #print axioms Crdt.merge_bot

/-- info: 'Crdt.le_merge_left' does not depend on any axioms -/
#guard_msgs in #print axioms Crdt.le_merge_left

/-- info: 'Crdt.le_merge_right' does not depend on any axioms -/
#guard_msgs in #print axioms Crdt.le_merge_right

/-- info: 'Crdt.merge_least' does not depend on any axioms -/
#guard_msgs in #print axioms Crdt.merge_least

-- G-Counter convergence headlines (`Crdt.Instances`).

/-- info: 'Crdt.gcounter_merge_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Crdt.gcounter_merge_apply

/-- info: 'Crdt.gcounter_strong_eventual_consistency' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Crdt.gcounter_strong_eventual_consistency

/-- info: 'Crdt.gcounter_eventual_agreement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Crdt.gcounter_eventual_agreement

-- Causal-Cut Consumable Authority — the authority frontier, necessity v0
-- (`Crdt.AuthorityFrontier`).

/-- info: 'Crdt.AuthorityFrontier.no_disconnected_double_availability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Crdt.AuthorityFrontier.no_disconnected_double_availability

/-- info: 'Crdt.AuthorityFrontier.authority_frontier_card_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Crdt.AuthorityFrontier.authority_frontier_card_le_one

/-- info: 'Crdt.AuthorityFrontier.double_consume_countermodel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Crdt.AuthorityFrontier.double_consume_countermodel

/-- info: 'Crdt.AuthorityFrontier.copy_frontier_init_card_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Crdt.AuthorityFrontier.copy_frontier_init_card_two

/-- info: 'Crdt.AuthorityFrontier.ccca_teeth_double_consume' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Crdt.AuthorityFrontier.ccca_teeth_double_consume

/-- info: 'Crdt.AuthorityFrontier.ccca_teeth_both_live' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Crdt.AuthorityFrontier.ccca_teeth_both_live

/-- info: 'Crdt.AuthorityFrontier.ccca_edge_only_still_unsafe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Crdt.AuthorityFrontier.ccca_edge_only_still_unsafe

/-- info: 'Crdt.AuthorityFrontier.ccca_safe_world_safe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Crdt.AuthorityFrontier.ccca_safe_world_safe

/-- info: 'Crdt.AuthorityFrontier.ccca_safe_world_transfer_live' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Crdt.AuthorityFrontier.ccca_safe_world_transfer_live

/--
info: 'Crdt.AuthorityFrontier.ccca_safe_world_no_double_availability' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms Crdt.AuthorityFrontier.ccca_safe_world_no_double_availability

-- Sealed-handoff sufficiency (`Crdt.AuthorityFrontier`, third mesh brick).

/-- info: 'Crdt.AuthorityFrontier.sealed_handoff_safe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Crdt.AuthorityFrontier.sealed_handoff_safe

/-- info: 'Crdt.AuthorityFrontier.wSafe_sealed_handoff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Crdt.AuthorityFrontier.wSafe_sealed_handoff

/-- info: 'Crdt.AuthorityFrontier.wEdgeOnly_not_sealed_handoff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Crdt.AuthorityFrontier.wEdgeOnly_not_sealed_handoff

/-- info: 'Crdt.AuthorityFrontier.wSeq_safe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Crdt.AuthorityFrontier.wSeq_safe

/-- info: 'Crdt.AuthorityFrontier.wSeq_not_sealed_handoff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Crdt.AuthorityFrontier.wSeq_not_sealed_handoff

/-- info: 'Crdt.AuthorityFrontier.gap_vacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Crdt.AuthorityFrontier.gap_vacuous

-- Sufficiency lifted to the (generated) abstract system
-- (`Crdt.AuthorityFrontier`, Layer D — fourth mesh brick).

/-- info: 'Crdt.AuthorityFrontier.sufficiency_needs_generation' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Crdt.AuthorityFrontier.sufficiency_needs_generation

/-- info: 'Crdt.AuthorityFrontier.sealed_senders_safe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Crdt.AuthorityFrontier.sealed_senders_safe

/-- info: 'Crdt.AuthorityFrontier.copy_not_sealed_senders' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Crdt.AuthorityFrontier.copy_not_sealed_senders

/-- info: 'Crdt.AuthorityFrontier.wSafe_sender_never_live' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Crdt.AuthorityFrontier.wSafe_sender_never_live

/-- info: 'Crdt.AuthorityFrontier.seq_safe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Crdt.AuthorityFrontier.seq_safe

/-- info: 'Crdt.AuthorityFrontier.seq_both_live_init' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Crdt.AuthorityFrontier.seq_both_live_init

/-- info: 'Crdt.AuthorityFrontier.seq_not_sealed_senders' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Crdt.AuthorityFrontier.seq_not_sealed_senders

-- Normal form STEP-0 enumerator + shape probe
-- (`Crdt.AuthorityFrontier`, Layer E).

/-- info: 'Crdt.AuthorityFrontier.step0_alternative_expressible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Crdt.AuthorityFrontier.step0_alternative_expressible

/-- info: 'Crdt.AuthorityFrontier.step0_gap_world_expressible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Crdt.AuthorityFrontier.step0_gap_world_expressible

/-- info: 'Crdt.AuthorityFrontier.step0_seal_shape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Crdt.AuthorityFrontier.step0_seal_shape

/-- info: 'Crdt.AuthorityFrontier.step0_seq_shape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Crdt.AuthorityFrontier.step0_seq_shape

/-- info: 'Crdt.AuthorityFrontier.probeWorld_irrefl' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Crdt.AuthorityFrontier.probeWorld_irrefl

/-- info: 'Crdt.AuthorityFrontier.probeWorld_107' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Crdt.AuthorityFrontier.probeWorld_107

/-- info: 'Crdt.AuthorityFrontier.probeWorld_2' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Crdt.AuthorityFrontier.probeWorld_2

-- The handoff-or-gap NORMAL FORM (`Crdt.AuthorityFrontier`, Layer F).

/-- info: 'Crdt.AuthorityFrontier.both_fires_unsafe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Crdt.AuthorityFrontier.both_fires_unsafe

/-- info: 'Crdt.AuthorityFrontier.dead_potential_safe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Crdt.AuthorityFrontier.dead_potential_safe

/-- info: 'Crdt.AuthorityFrontier.safeCuts_iff_dead_potential' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Crdt.AuthorityFrontier.safeCuts_iff_dead_potential

/-- info: 'Crdt.AuthorityFrontier.dead_trichotomy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Crdt.AuthorityFrontier.dead_trichotomy

/-- info: 'Crdt.AuthorityFrontier.authority_normal_form' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Crdt.AuthorityFrontier.authority_normal_form

/-- info: 'Crdt.AuthorityFrontier.everLive_iff_fires' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Crdt.AuthorityFrontier.everLive_iff_fires

/-- info: 'Crdt.AuthorityFrontier.safeCuts_iff_ever_live_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Crdt.AuthorityFrontier.safeCuts_iff_ever_live_unique

/-- info: 'Crdt.AuthorityFrontier.safe_cut_dichotomy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Crdt.AuthorityFrontier.safe_cut_dichotomy

/-- info: 'Crdt.AuthorityFrontier.sealedHandoff_iff_sealWitnessed' depends on axioms: [propext] -/
#guard_msgs in #print axioms Crdt.AuthorityFrontier.sealedHandoff_iff_sealWitnessed

-- No silent handoff — the abstract fragment
-- (`Crdt.AuthorityFrontier`, Layer G).

-- Mathlib v4.35.0: `Finset.mem_insert_self` / `Finset.mem_insert_of_mem` now depend on
-- `Classical.choice`, so this footprint grew from [propext, Quot.sound]. Still baseline.
/-- info: 'Crdt.AuthorityFrontier.live_persists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Crdt.AuthorityFrontier.live_persists

/-- info: 'Crdt.AuthorityFrontier.no_silent_handoff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Crdt.AuthorityFrontier.no_silent_handoff

/-- info: 'Crdt.AuthorityFrontier.handoff_needs_connection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Crdt.AuthorityFrontier.handoff_needs_connection

-- zrdt: exactly the advertised statements about the shipped store (`Crdt/Merkle/Api.lean`,
-- docs/PLAN.md §3.2), in the order of §3.2, and `Zrdt.encode_injective`
-- (`Crdt/Merkle/EncodeProofs.lean`), the same names as `comparator.json`. Some of their proof
-- obligations are pinned in a separate block below; they are not advertised.

/-- info: 'Zrdt.CheckedStore.fetched' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Zrdt.CheckedStore.fetched

/-- info: 'Zrdt.CheckedStore.no_collision' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Zrdt.CheckedStore.no_collision

/-- info: 'Zrdt.CheckedStore.agree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Zrdt.CheckedStore.agree

/-- info: 'Zrdt.CheckedStore.abs_accept' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Zrdt.CheckedStore.abs_accept

/-- info: 'Zrdt.CheckedStore.abs_merge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Zrdt.CheckedStore.abs_merge

/-- info: 'Zrdt.CheckedStore.open_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Zrdt.CheckedStore.open_iff

/-- info: 'Zrdt.CheckedStore.salvage_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Zrdt.CheckedStore.salvage_spec

/-- info: 'Zrdt.CheckedStore.encode_open' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Zrdt.CheckedStore.encode_open

/-- info: 'Zrdt.CheckedStore.confirmed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Zrdt.CheckedStore.confirmed

/-- info: 'Zrdt.CheckedStore.classify_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Zrdt.CheckedStore.classify_spec

/-- info: 'Zrdt.encode_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Zrdt.encode_injective

-- Added for joining (docs/JOIN_PLAN.md §7.3): `agree_rel` for a view with a boundary, and the
-- content statements of `SERVE`, in `Api.lean` and `comparator.json` with the others.

/-- info: 'Zrdt.CheckedStore.agree_rel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Zrdt.CheckedStore.agree_rel

/-- info: 'Zrdt.CheckedStore.serve_content' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Zrdt.CheckedStore.serve_content

/-- info: 'Zrdt.CheckedStore.serve_content_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Zrdt.CheckedStore.serve_content_complete

-- Proof obligations, NOT advertised. These are the spec theorems the advertised statements
-- above stand on (`Crdt/Merkle/Chat.lean`), and facts about the shipped code's commitment
-- checks (`core/Zrdt/Proto.lean`, `core/Zrdt/Commit.lean`). They are pinned so that a `sorry` or a new
-- axiom in them fails the build too; they are not part of what docs/PLAN.md §3.2 promises, and
-- `comparator.json` does not list them.

/-- info: 'Crdt.Merkle.authorConfirmed_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Crdt.Merkle.authorConfirmed_sound

/-- info: 'Crdt.Merkle.salvage_maximal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Crdt.Merkle.salvage_maximal

/-- info: 'Crdt.Merkle.confirmed_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Crdt.Merkle.confirmed_exact

/-- info: 'Crdt.Merkle.fetched_union' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Crdt.Merkle.fetched_union

/-- info: 'Zrdt.Proto.acceptRecord_accepted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Zrdt.Proto.acceptRecord_accepted

/-- info: 'Zrdt.openingMatches_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Zrdt.openingMatches_spec

-- `COMMIT`'s opening always passes `openingMatches` (`core/Zrdt/Commit.lean`, `Proto.lean`).

/-- info: 'Zrdt.committedBytes_idem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Zrdt.committedBytes_idem

/-- info: 'Zrdt.commitWithOpening_matches' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Zrdt.commitWithOpening_matches

/-- info: 'Zrdt.Proto.commit_openingMatches' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Zrdt.Proto.commit_openingMatches

-- Join spec obligations, NOT advertised (docs/JOIN_PLAN.md §7.2, `Crdt/Merkle/Rel.lean`): a
-- newcomer's relative store, with a boundary of opaque digests, served by a closed or a relative
-- responder. They are proof obligations for the join work; `comparator.json` does not list them.

/-- info: 'Crdt.Merkle.served_heads'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Crdt.Merkle.served_heads'

/-- info: 'Crdt.Merkle.served_closed'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Crdt.Merkle.served_closed'

/-- info: 'Crdt.Merkle.served_tight'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Crdt.Merkle.served_tight'

/-- info: 'Crdt.Merkle.served_boundary'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Crdt.Merkle.served_boundary'

/-- info: 'Crdt.Merkle.agree_rel'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Crdt.Merkle.agree_rel'

/-- info: 'Crdt.Merkle.newcomer_agree'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Crdt.Merkle.newcomer_agree'

-- SERVE (docs/JOIN_PLAN.md §5, §7.1; `core/Zrdt/Serve.lean`, `core/Zrdt/Proto.lean`). The
-- running-code statements, NOT advertised under these names: `Api.lean` advertises
-- `serve_content` and `serve_content_complete` as `CheckedStore.serve_content` and
-- `CheckedStore.serve_content_complete`, stated over `abs c` (pinned above).

/-- info: 'Zrdt.Serve.serveOpening_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Zrdt.Serve.serveOpening_spec

/-- info: 'Zrdt.Serve.serve_content' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Zrdt.Serve.serve_content

/-- info: 'Zrdt.Serve.serve_content_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Zrdt.Serve.serve_content_complete

/-- info: 'Zrdt.Serve.serve_authorCopy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Zrdt.Serve.serve_authorCopy

/-- info: 'Zrdt.Serve.serve_strict' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Zrdt.Serve.serve_strict

/-- info: 'Zrdt.Serve.serve_export' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Zrdt.Serve.serve_export

/-- info: 'Zrdt.Serve.serve_after' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Zrdt.Serve.serve_after

/-- info: 'Zrdt.Serve.serve_boundary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Zrdt.Serve.serve_boundary

/-- info: 'Zrdt.Serve.audience_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Zrdt.Serve.audience_bound

/-- info: 'Zrdt.Proto.accept_accepted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Zrdt.Proto.accept_accepted

/-- info: 'Zrdt.Proto.accept_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Zrdt.Proto.accept_refused

/-- info: 'Zrdt.Proto.run_serve_content' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Zrdt.Proto.run_serve_content

/-- info: 'Zrdt.Proto.run_audience' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Zrdt.Proto.run_audience

/-- info: 'Zrdt.Proto.run_addressed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Zrdt.Proto.run_addressed

-- The relative store (docs/JOIN_PLAN.md §6.2, §7.1; `core/Zrdt/RelStore.lean`,
-- `core/Zrdt/ChatStore.lean`, `core/Zrdt/Proto.lean`). Not advertised yet: JOIN_PLAN §7.3.

/-- info: 'Zrdt.builtRel_empty_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Zrdt.builtRel_empty_iff

/-- info: 'Zrdt.rawAcceptRel_empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Zrdt.rawAcceptRel_empty

/-- info: 'Zrdt.rawAcceptRel_built' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Zrdt.rawAcceptRel_built

/-- info: 'Zrdt.RelStore.acceptAll_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Zrdt.RelStore.acceptAll_sound

/-- info: 'Zrdt.RelStore.acceptAll_stuck' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Zrdt.RelStore.acceptAll_stuck

/-- info: 'Zrdt.RelStore.load_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Zrdt.RelStore.load_complete

/-- info: 'Zrdt.RelStore.load_reopens' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Zrdt.RelStore.load_reopens

/-- info: 'Zrdt.RelStore.merge_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Zrdt.RelStore.merge_ok

/-- info: 'Zrdt.RelStore.linkable_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Zrdt.RelStore.linkable_sub

/-- info: 'Zrdt.ChatStore.encode_reopens' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Zrdt.ChatStore.encode_reopens

/-- info: 'Zrdt.Proto.acceptView_built' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Zrdt.Proto.acceptView_built

/-- info: 'Zrdt.ChatStore.acceptAll_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Zrdt.ChatStore.acceptAll_sound

/-- info: 'Zrdt.ChatStore.linkable_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Zrdt.ChatStore.linkable_sub

/-- info: 'Zrdt.classify_raw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Zrdt.classify_raw

/-- info: 'Zrdt.Proto.acceptView_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Zrdt.Proto.acceptView_sound

/-- info: 'Zrdt.Proto.acceptView_accepted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Zrdt.Proto.acceptView_accepted

/-- info: 'Zrdt.Proto.acceptView_audiences' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Zrdt.Proto.acceptView_audiences

/-- info: 'Zrdt.Proto.run_acceptView' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Zrdt.Proto.run_acceptView

-- Boundary admission (docs/JOIN_PLAN.md §4.4, round 2): a per-digest `ACCEPT_VIEW` keeps a
-- boundary digest only if a stored record links it, so it adds no head that is not a stored record.

/-- info: 'Zrdt.rawAcceptRel_fst_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Zrdt.rawAcceptRel_fst_mono

/-- info: 'Zrdt.RelStore.prune_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Zrdt.RelStore.prune_spec

/-- info: 'Zrdt.ChatStore.prune_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Zrdt.ChatStore.prune_spec

/-- info: 'Zrdt.ChatStore.accept_fst_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Zrdt.ChatStore.accept_fst_mono

/-- info: 'Zrdt.Proto.acceptView_boundary_linked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Zrdt.Proto.acceptView_boundary_linked

/-- info: 'Zrdt.Proto.acceptView_heads' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Zrdt.Proto.acceptView_heads

/-- info: 'Zrdt.Proto.run_acceptView_heads' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Zrdt.Proto.run_acceptView_heads

/-- info: 'Zrdt.Proto.run_linkable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Zrdt.Proto.run_linkable

/-- info: 'Zrdt.Proto.run_newRelative' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Zrdt.Proto.run_newRelative

-- The bridge from `SERVE` to the spec, NOT advertised (docs/JOIN_PLAN.md §7.2,
-- `Crdt/Merkle/ServeAbs.lean`): the catch-up reply is the spec's served view, so a newcomer
-- gets the responder's heads, a closed and tight view, and boundary digests that hide nothing.

/-- info: 'Zrdt.Serve.serve_abs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Zrdt.Serve.serve_abs

/-- info: 'Zrdt.Serve.serve_heads' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Zrdt.Serve.serve_heads

/-- info: 'Zrdt.Serve.serve_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Zrdt.Serve.serve_closed

/-- info: 'Zrdt.Serve.serve_tight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Zrdt.Serve.serve_tight

/-- info: 'Zrdt.Serve.serve_boundary_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Zrdt.Serve.serve_boundary_spec

/-- info: 'Zrdt.Serve.serve_after_reaches' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Zrdt.Serve.serve_after_reaches

/-- info: 'Zrdt.CheckedStore.closedRel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Zrdt.CheckedStore.closedRel

/-- info: 'Zrdt.CheckedStore.tightRel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Zrdt.CheckedStore.tightRel

def main : IO Unit :=
  IO.println "axiom gate passed: all checks pinned by #guard_msgs at compile time"
