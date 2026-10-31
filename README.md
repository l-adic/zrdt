# zrdt

Replicated data types (CRDTs) in Lean 4, with machine-checked proofs.

```
make install   # fetch the Mathlib cache and build
make run       # run the axiom gate
```

Lean v4.35.0, Mathlib v4.35.0. Phase 0 (`Crdt/*.lean`) proves that replicas which merge
states by join agree once they have seen the same updates. Phase 1 (`Crdt/Merkle/`) is below.

## Phase 1: hash-linked records

A replica stores a set of **records**. Each record has a payload, the hashes of the records its
author had seen (its **links**), and an author name. Merging two replicas is set union, so the
phase 0 convergence results apply as they are.

Peers and the network are not trusted. A replica checks only two things: hashes, and whether a
record's links resolve to records it holds.

### What is proved

| Theorem | In plain words |
|---|---|
| `fetched_agree` | Two replicas that fetched everything reachable from the same heads, and nothing else, hold the same store. Or two records in their stores have the same hash. |
| `merge_fetched` | So they still agree after each merges in the same records of its own. |
| `fetched_build` | A replica that accepts records one at a time, each only once its links resolve, is fetched from its own heads. Or two of its records have the same hash. So honest replicas meet the hypotheses of `fetched_agree`. |
| `closed_accept`, `closed_union` | If you hold a record, you hold what it was built on. Accepting and merging keep this true. |
| `heads_insert` | After a new record is accepted, the heads are its hash plus the old heads it did not link. Or a collision. |
| `eq_of_digests_eq` | Two stores with the same set of hashes are the same store. Or a collision. |
| `TaskList.add_wins` | A task added on one replica survives a merge with a replica that had not seen the add, even if that replica removed the same title. Or a collision. |
| `TaskList.remove_removes_only` | A remove takes the task off the list when it was the only add of that title. |
| `TaskList.fetched_live_agree` | Two replicas that fetched the same heads show the same task list. Or a collision. |

**How collisions appear.** `hash` is a plain function parameter. Nothing assumes it is
injective. Integrity theorems end in `∨ CollisionIn hash u`: two *different records inside the
stores `u`* have the same hash. A real hash always has collisions somewhere (fixed output size,
unbounded inputs), so a global "a collision exists" would make every theorem trivially true.
`CollisionIn` points to the colliding records the replicas actually hold. The `_global` versions
in `Integrity.lean` give the weaker `∨ Collision hash`.

**The task list.** A remove counts only if it also links the record it removes, so its author
must have seen it. A remove that does not link its target does nothing.

**Examples.** `TaskList.lean` ends with a scenario: Ann and Bob add tasks, Ann removes one, and
Bob adds it again before seeing the remove. Every main theorem is applied to it with all
hypotheses discharged by `decide`. The scenario also shows stores that the definitions reject: a
store with an extra made-up record (not `Tight`) and a store with a record swapped out (not
`Complete`).

### Trusted surface

- Axioms: only `propext`, `Classical.choice`, `Quot.sound`. `Test/Axioms.lean` pins this for
  the main theorems and runs on every `lake build`.
- No `sorry`, `native_decide`, `opaque` contracts or external tools.
- Definitions a reader must check, for `fetched_agree`: `Record`, `Store`, `CollisionIn`,
  `Reach`, `Complete`, `Tight`, `Fetched` (all in `Crdt/Merkle/Defs.lean`). `fetched_build`
  adds `digests`, `heads`, `accept`, `build`. The task-list theorems add `Op`, `Removes`, `live`,
  `Closed`.

### Not proved

- **Who wrote a record.** `author` is an unchecked claim. Anyone can write any record.
  Signatures are phase 2.
- **Forgery and equivocation.** An author can write two conflicting records. Both are kept, and
  nothing detects it.
- **That the hash resists collisions.** The theorems only say that when replicas disagree, a
  collision exists in their stores.
- **Arrival order for single records.** `accept` drops a record whose links have not arrived yet
  (`build [rC, rA, rB]` keeps only `rA`, `rB`). Convergence is proved for merging whole stores,
  not for a stream of single accepts. Holding early records until their links arrive is not
  modelled.
- **Compaction.** Stores only grow.
- **Comparator.** Not run yet. It is planned for the end of the project.
