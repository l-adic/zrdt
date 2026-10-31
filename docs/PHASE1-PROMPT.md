# Task: add a hash-linked (authenticated) record layer to the zrdt Lean library — phase 1

## Where you are

Repo: `~/code/zrdt` (github.com/l-adic/zrdt), Lean 4.35.0, Mathlib v4.35.0, Lake. Read first, in this
order: `claude.md`, `rules.md`, `Crdt/Defs.lean`, `Crdt/Convergence.lean`, `Crdt/ORSet.lean`,
`Test/Axioms.lean`, `lakefile.toml`. Follow `claude.md` strictly: one `lake` process at a time, build one
module per edit (`lake build Crdt.Foo`), no `sorry`/`admit`/new axioms/`native_decide`, standard axioms
only (`propext`, `Classical.choice`, `Quot.sound`), specs in plain English with a docstring and a concrete
example per definition, every main theorem instantiated on a concrete input with all hypotheses
discharged, and at least one `¬ Spec bad` example. `lake build` must pass and `lake exe axiom_check`
must print "axiom gate passed".

## Phase 0: what the library already proves (do not change any of it)

Namespace `Crdt`. A state-based CRDT carrier is any `S` with `SemilatticeSup S`, `OrderBot S`,
`DecidableEq S`. `merge a b := a ⊔ b`, initial state `⊥`, `replicaState (u : Finset S) := u.sup id`.
Key theorems: `merge_comm/assoc/idem`, `fold_merge_eq_replicaState`, `strong_eventual_consistency`
(equal delivered sets ⇒ equal folded state), `merge_replicaState` (gossip = union),
`DeliverySystem.eventual_agreement` (conditional liveness). Instances: G-Set (`Finset α`), G-Counter,
PN-Counter, `Crdt.ORSet` (add-wins over abstract tokens), `Crdt.RGA` (sequence over abstract positions).
`Test/Axioms.lean` pins axiom footprints with `#guard_msgs`; it runs on every `lake build`.

Phase 0 assumes every delivered state is genuine, exchanges whole states, and takes token/position
uniqueness as a hypothesis. Phase 1 removes those three assumptions for the data layer.

## Background: authenticated data structures, and which part we keep

An authenticated data structure (ADS) lets a party holding only a short digest check answers computed
by an untrusted party holding the data. Merkle (1979) did it for arrays; Miller, Hicks, Katz, Shi,
"Authenticated Data Structures, Generically" (POPL 2014) did it for any functional data structure via
the λ• calculus: a prover and a verifier run the same code, the prover emits a stream of hashed
"shallow projections", the verifier replays against its digest. Correctness: honest prover ⇒ verifier
gets the right answer. Security: if the verifier accepts a wrong answer, the trace yields a hash
collision.

That threat model (one trusted digest, one untrusted server) does not match a CRDT, where every
replica contributes and there is no authoritative digest. So we do NOT port the prover/verifier
calculus. We keep the one idea that transfers: **content addressing with hash links**, the Merkle-DAG
lineage of git, IPFS Merkle-CRDTs (Sanjuán et al. 2020) and hash graphs (Kleppmann 2022). Each record
names its causal predecessors by hash. The state is a finite set of records, merge is set union, so
all of phase 0 applies verbatim. What hash links add:

- integrity against a tampering server or network (a swapped record changes its hash),
- incremental sync (exchange heads, fetch missing records by digest) instead of whole states,
- unique identifiers for free (a record's hash is its token), discharging phase 0's allocator hypothesis,
- checkable causal order via a closure rule: merge a record only when its links resolve.

What they do not add: attribution. Anyone can write any record. Signatures are phase 2.

## Modeling discipline (non-negotiable)

- `hash` is a bare function parameter `Record → H`. No injectivity, no collision-resistance axiom.
- Define `Collision hash : Prop := ∃ x y, x ≠ y ∧ hash x = hash y`.
- Every integrity theorem concludes `correct ∨ Collision hash`. The collision is a concrete witness in
  the conclusion, never a hypothesis. That is how the POPL'14 security theorem is phrased, and it keeps
  the axiom gate at baseline.
- The runtime check is hash equality and link resolution, nothing else. The verifier cannot observe a
  collision; only the theorem mentions it.
- Executable definitions must be computable (no `Classical` in data). Provide `Decidable` instances so
  `decide` and `#guard` work on small examples.

## Phase 1 vocabulary (namespace `Crdt.Merkle`, new files under `Crdt/Merkle/`)

Type parameters: payload `α`, digest `H` with `DecidableEq H`, author/identity `K` with `DecidableEq K`.
Use `H` for digests; `D` is taken by `Crdt.AuthorityFrontier` for failure domains.

```lean
structure Record (α H K : Type*) where
  payload : α
  links   : Finset H   -- hashes of the records the author had seen (its local heads at write time)
  author  : K          -- a plain claim in phase 1; becomes a verified key in phase 2
deriving DecidableEq

abbrev Store (α H K) := Finset (Record α H K)          -- merge is ∪, ⊥ is ∅ (phase 0 applies)

variable (hash : Record α H K → H)
def Collision : Prop := ∃ x y : Record α H K, x ≠ y ∧ hash x = hash y
def digests (s : Store α H K) : Finset H := s.image hash
def Closed  (s : Store α H K) : Prop := ∀ r ∈ s, ∀ d ∈ r.links, ∃ r' ∈ s, hash r' = d
def heads   (s : Store α H K) : Finset H :=
  (s.filter fun r ↦ ∀ r' ∈ s, hash r ∉ r'.links).image hash
-- reachability from a head set, and the two halves of "this store was fetched from these heads"
inductive Reach (s : Store α H K) (hs : Finset H) : H → Prop
  | head {d} : d ∈ hs → Reach s hs d
  | link {r d} : r ∈ s → Reach s hs (hash r) → d ∈ r.links → Reach s hs d
def Complete (s) (hs) : Prop := ∀ d, Reach hash s hs d → ∃ r ∈ s, hash r = d   -- fetched everything reachable
def Tight    (s) (hs) : Prop := ∀ r ∈ s, Reach hash s hs (hash r)              -- fetched only reachable things
def Fetched  (s) (hs) : Prop := Complete hash s hs ∧ Tight hash s hs
structure Receipt (H) where digest : H; heads : Finset H   -- what a store returns after merging one record
```

## Theorems to prove (statements are the contract; keep them this shape)

Structure (`Crdt/Merkle/Defs.lean`):
1. `closed_empty : Closed hash ∅` and `closed_union : Closed hash s → Closed hash t → Closed hash (s ∪ t)`.
   Plain English: if you hold a record you hold what it was built on, and union keeps that true.
2. `digests_union : digests hash (s ∪ t) = digests hash s ∪ digests hash t`, `digests_empty`.
   (The digest view is a join-homomorphism; `Finset.image_union`.)
3. `mem_heads`: characterise membership; `heads_subset_digests`.
4. `strong_eventual_consistency` and `eventual_agreement` re-exported at `Store α H K`, as
   `Crdt.ORSet` does.

Integrity (`Crdt/Merkle/Integrity.lean`), each with the collision disjunct:
5. `accept_unique : hash a = d → hash b = d → a = b ∨ Collision hash`. The kernel; two lines.
6. `subset_of_digests_subset : digests hash s ⊆ digests hash t → s ⊆ t ∨ Collision hash` and
   `eq_of_digests_eq`. Digest sets determine stores.
7. `reach_mono_of_complete : ¬ Collision hash → Complete hash t hs → ∀ d, Reach hash s hs d → Reach hash t hs d`
   (induction on `Reach`).
8. `subset_of_fetched : ¬ Collision hash → Complete hash t hs → Tight hash s hs → s ⊆ t`.
9. `fetched_agree : Fetched hash s hs → Fetched hash t hs → s = t ∨ Collision hash`. **Headline.** Two
   replicas that fetched the same heads from untrusted sources hold the same store, or a collision exists.
10. `merge_fetched : Fetched hash s hs → Fetched hash t hs → merge own s = merge own t ∨ Collision hash`.
    Integrity composes with convergence.
11. `receipt_heads_sound`: the heads in a receipt are the heads of the merged store (define the receipt
    function and prove it is what it says).

Grounding instance (`Crdt/Merkle/TaskList.lean`), an add-wins shared task list:
```lean
inductive Op (H) | add (title : String) | remove (target : H)   -- target = hash of the add record
def live (hash) (s : Store (Op H) H K) : Finset String :=
  { title | add record a ∈ s, no remove record in s targets hash a }   -- write it as a Finset.filter/image
```
12. `live_determined`: equal stores give equal task lists (trivial, but it is the spec a reader wants).
13. `add_wins`: an add record not targeted by any remove in `s` is live after merging any `s'` whose
    removes do not target it; and the concurrent re-add case: a fresh add has a fresh hash, so an
    existing remove does not target it, or a collision exists.
14. `remove_requires_closure`: in a closed store, every remove's target resolves to a record in the store.
15. `remove_removes`: a remove targeting hash a makes a's title absent unless another add with the same
    title is live. Then `¬`-examples: a store where the task is removed is rejected by `live`.

Examples: a 3-record scenario (`g`, `rA = add "buy milk"` linking `{hash g}`, `rB = add "call mom"`
linking `{hash g}`, `rC = remove (hash rA)` linking `{hash rA, hash rB}`) with a toy injective `hash`
(e.g. an index into a fixed list) so everything is `decide`-able: closure holds, heads before/after
`rC` are `{hA, hB}` then `{hC}`, `live = {"call mom"}` regardless of insertion order (`#guard` with two
orders). Also one example showing `Fetched` for the honest store and a tampered store that is not `Tight`.

## Wiring

- Add `import Crdt.Merkle.Defs/Integrity/TaskList` to `Crdt.lean`.
- Add `#guard_msgs in #print axioms` lines to `Test/Axioms.lean` for theorems 5, 9, 10, 13. Expect
  `[propext, Classical.choice, Quot.sound]` or fewer; copy the exact message Lean prints.
- Keep the Makefile targets working (`make install`, `make run`).
- Add a short section to a new `README.md`: what phase 1 proves, the trusted surface (none beyond the
  standard axioms; `hash` is a parameter), and what it does not prove (attribution, forgery, Byzantine
  equivocation, compaction).

## Out of scope for this task

Signatures and a `Forgery` disjunct (phase 2: a `sig` field on `Record`, `verify : K → Record → Sig → Prop`,
an honest-signing log, per-key well-formedness). zkSNARK receipts. Open membership and key revocation.
History compaction. Do not add a prover/verifier calculus. Do not modify any phase 0 statement.

## Working style

Skeleton first: state every definition and theorem with `sorry`, check the headline (`fetched_agree`)
follows from its lemmas, then fill proofs one at a time, building the single module after each edit.
Prefer `Finset.mem_image`, `Finset.mem_filter`, `Finset.mem_union`, `Finset.image_union`,
`Finset.Subset.antisymm`. If a statement resists, test it with `plausible` or a counterexample before
changing the proof approach; never weaken a statement silently. Report at the end: files added,
theorems proved, axiom footprints, anything left out and why.
