# Visibility audit of `Crdt/` (phase 0)

Scan of every declaration in the seven `Crdt` modules, with where each one is referenced. Comments and
docstrings were stripped before counting, so only code references count. Generated 2026-10-31 against
commit `0433772`.

## Rules used

A declaration must stay **public** if any of these hold:

1. **Cross-module.** Another `Crdt` module references it. (Short-name collisions were checked against
   the import graph: `Defs → Convergence → Liveness → {Instances, ORSet, Sequence}`; `AuthorityFrontier`
   imports only Mathlib.)
2. **Gate.** `Test/Axioms.lean` runs `#print axioms` on it. Private names are file-scoped and the gate
   cannot resolve them.
3. **In a public statement.** It appears in the statement (not the proof) of a public theorem. A private
   name inside a public statement makes that theorem unusable from outside.
4. **Abbrev ingredient.** It appears in the body of a public `abbrev`. Abbrevs unfold, so the name
   surfaces in users' goals.
5. **Declared API.** It is named in the crdt-lean README theorem inventory or `docs/AUTHORITY-FRONTIER.md`.
   These are the library's product even when no code references them.
6. **Cross-file simp.** It is `@[simp]` and another module's `simp` relies on it.

Everything else is a **private** candidate. Within those, **dead** means no reference anywhere.
**Body-only** means used only inside the bodies of public `def`s: `private` is legal, but the mangled
name leaks when a user unfolds that def.

## Summary

| Module | Decls | Private candidates | Of which dead | Public, unused in code (API only) |
|---|---|---|---|---|
| Defs | 12 | 0 | 0 | 7 (gate-cited algebra lemmas) |
| Convergence | 8 | 1 | 1 | 5 |
| Liveness | 6 | 0 | 0 | 3 |
| Instances | 16 | 1 | 1 | 10 |
| ORSet | 15 | 5 | 0 | 3 |
| Sequence | 16 | 4 | 1 | 8 |
| AuthorityFrontier | 105 + 4 instances | 29 | 9 | 0 |
| **Total** | **178 + 4** | **40** | **12** | **36** |

## Defs.lean — nothing to privatize

| Declaration | Verdict | Reason |
|---|---|---|
| `merge`, `merge_def`, `replicaState`, `replicaState_insert` | public | cross-module |
| `replicaState_empty` | public | `@[simp]`, used by `simp` in Convergence |
| `merge_comm`, `merge_assoc`, `merge_idem`, `merge_bot`, `le_merge_left`, `le_merge_right`, `merge_least` | public | gate |

## Convergence.lean

| Declaration | Verdict | Reason |
|---|---|---|
| `strong_eventual_consistency`, `replicaState_mono` | public | cross-module |
| `fold_merge_eq_replicaState` | public | API (README 5); only used by SEC in-file |
| `replicaState_redeliver`, `le_replicaState`, `replicaState_le`, `merge_replicaState` | public, unused | API (README 7, 8, 10) |
| `converged_states_agree` | **private, dead** | not cited anywhere; restates `Finset.union_comm` |

## Liveness.lean — nothing to privatize

| Declaration | Verdict | Reason |
|---|---|---|
| `DeliverySystem`, `DeliverySystem.eventual_agreement` | public | cross-module |
| `eventually_covers`, `DeliverySystem.converges`, `DeliverySystem.reaches_converged` | public | API (README 11–13); in-file helpers otherwise |
| `DeliverySystem.convergedState` | public | in statement of `reaches_converged` |

## Instances.lean

| Declaration | Verdict | Reason |
|---|---|---|
| `GCounter`, `gcounter_merge_apply`, `gcounter_strong_eventual_consistency`, `gcounter_eventual_agreement` | public | gate / in gate statements |
| `PNCounter`, `gcounterValue` | public | in public statements |
| `gset_*` (4), `gcounter_value_le_merge`, `gcounterValue_mono`, `pncounter_*` (3) | public, unused | API (README 15) |
| `pncounterValue` | **private, dead** | defined, but no theorem mentions it |

## ORSet.lean

| Declaration | Verdict | Reason |
|---|---|---|
| `State`, `lookup`, `add`, `remove` | public | in public statements |
| `add_wins` | public | gate |
| `add_lookup`, `remove_lookup_false` | public | API (README 17, 18) |
| `lookup_iff`, `strong_eventual_consistency`, `eventual_agreement` | public, unused | API; `lookup_iff` is the only public way to reason about `lookup` |
| `mem_elements` | **private** | helper; `lookup_iff` is its public face |
| `t_mem_observedTokens` | **private** | helper |
| `merge_eq` | **private** | used once, in `add_wins` proof |
| `observedTokens` | **private, body-only** | used in `remove` body and one helper |
| `elements` | **private, body-only** | used in `lookup` body and one helper |

## Sequence.lean

| Declaration | Verdict | Reason |
|---|---|---|
| `State`, `read`, `live`, `insert`, `delete` | public | in public statements |
| `read_sorted`, `read_determined`, `delete_not_read`, `insert_read`, `read_strong_eventual_consistency` | public, unused | API (README 19–21) |
| `read_nodup`, `eventual_agreement` | public, unused | API (module docstring) |
| `mem_positions`, `mem_read` | **private** | helpers; no external theorem needs them |
| `positions` | **private, body-only** | used in `read` body and the two helpers |
| `merge_eq` | **private, dead** | never used (the cross-file hits are `ORSet.merge_eq`) |

## AuthorityFrontier.lean

Public by gate (44 theorems) or by appearing in gate statements (35 defs, abbrevs, structures), plus the
`pe*` projections and `past`, which are ingredients of public abbrevs. Private candidates:

| Declaration | Verdict | Reason |
|---|---|---|
| `CopyConfig`, `copyOwn`, `CopyReach` | **private** | internals of `CopySystem`; users write `CopySystem.Config` |
| `probeEdge`, `probeStep`, `probeReach` | **private** | internals of `probeWorld` |
| `CutWorld.ext'`, `probeStep_lt`, `probeReach_lt` | **private** | proof helpers |
| `mem_past`, `consume_eq_two_or_five`, `mem_frontierAt`, `StepChain.reachable_of` | **private** | proof helpers |
| `seal_blocks_fires`, `wEdgeOnly_strict`, `wGap_strict` | **private** | used once each, in-file |
| `wUnsafe_strict`, `wSafe_strict`, `wSeq_strict` | **private, dead** | sanity facts; could become `example` |
| `wSafe_seal_edge`, `wEdgeOnly_no_seal_edge`, `wSeq_sender_live` | **private, dead** | probe evidence; could become `example` |
| `probeWorld_99`, `probeWorld_111`, `probeWorld_82` | **private, dead** | not gate-cited (107 and 2 are) |
| 4 anonymous `Decidable` instances (lines 356–359) | **private instance** | only needed for in-file `decide` |

Kept public on purpose: `peEnable`, `peDisable`, `peDomL`, `peConsume`, `CutWorld.past` (abbrev
ingredients); `both_fires_unsafe`, `dead_potential_safe`, `safeCuts_iff_dead_potential`,
`dead_trichotomy`, `everLive_iff_fires` (helpers in practice, but gate-cited).

## Observations

- The gate pins 55 names. Those plus the defs in their statements are the hard floor of the public
  surface; everything else public is there because the README calls it API.
- 36 public declarations are never referenced by code. They are the exported theorems. If the README
  inventory is not carried over to zrdt, several of them (`replicaState_redeliver`, `le_replicaState`,
  `replicaState_le`, `merge_replicaState`, `lookup_iff`, `read_nodup`) have no remaining reason to be public
  and could be reconsidered.
- Three definitions have no theorem about them at all: `pncounterValue`, `RGA.merge_eq`,
  `converged_states_agree`. `pncounterValue` is the notable one: the PN-Counter read is defined but
  nothing is proved about it.

## Phase 1: `Crdt/Merkle/` (88 declarations, audited after the phase 0 pass)

Same rules. Declared API here is the zrdt `README.md` table and trusted-surface list. 41 declarations
marked `private`.

| File | Private | Why |
|---|---|---|
| `Defs.lean` (12) | `Toy.R`, `Toy.hash`, `Toy.r0`, `Toy.r1`, `Toy.fake0` | example data for in-file `example`s |
| | `mem_heads` | helper for `heads_insert` |
| | `digests_union`, `digests_empty`, `closed_build`, `receipt_heads_sound`, `strong_eventual_consistency`, `eventual_agreement` | unused, not in README |
| `Integrity.lean` (7) | `subset_of_digests_subset`, `reach_mono_of_complete`, `subset_of_fetched`, `fetched_accept` | helpers for the gate-cited theorems |
| | `subset_of_digests_subset_global`, `reach_mono_of_complete_global`, `subset_of_fetched_global` | `_global` twins of helpers; the four `_global` twins of public theorems stay public (README names them) |
| `TaskList.lean` (22) | `Op.added` | body-only, used inside `live` |
| | `mem_live`, `fresh_add_not_removed`, `remove_removes` | helpers |
| | `live_determined`, `add_survives_merge` | unused, not in README |
| | all of `Scenario.*` (13 defs, 3 theorems) | example data and worked instances; re-expose if a demo executable needs them |

Kept public: everything gate-cited (8), everything another Merkle module references, every def in a
public statement, the three `Decidable` instances (needed for `decide` outside the file), and the
README-named theorems.
