# zrdt — project plan (for the lead agent)

Status date: 2026-10-31. Audience: the AI lead coordinating the work, and the agents it dispatches.
Ground truth for names, files, API and phases is the DECISIONS block this plan was derived from;
where this plan amends it, the amendment is marked **[amendment]** and needs the lead's sign-off.
Sibling documents: `PLAN_HUMANS.md` (the theorems and design in plain English) and `APP.md`
(Signal-Desktop integration detail). This file owns scope, contracts, phases, gates and rules.

## 1. Goal

**Pitch:** a verified transcript-consistency layer for group chat. Each message carries hash links
to the messages its sender had seen; clients verify links and heads; a malicious server cannot
drop, reorder, withhold, or rewrite history without detection.

Signal provides confidentiality and sender authentication. zrdt provides completeness and
consistency of the history. The core is written in Lean, proved in Lean, compiled to a C library,
and linked into a Signal-Desktop fork. Attacks are shown live against an "evil server":
Signal-Desktop's own mock Signal server (`packages/mock-server`, used by its integration tests) with
its delivery function overridden. A TLS proxy in front of Signal's staging server is the stretch for
a demo against the real network. Judging (rules.md) rewards an important property proved about the code
itself, plus a demo a non-technical person understands. Both are required; neither alone is enough.

**Non-goals** (say so in the README; never claim them):

- Attribution or signatures (Signal's job; `author` is carried, not checked by zrdt).
- Confidentiality (Signal's job; zrdt data rides inside Signal's encryption).
- Open membership, key revocation, or any defence against strangers.
- Timestamps, anchors, or any statement about real time.
- Compaction / bounded storage (history only grows).
- Signal-Android (stretch only, after the desktop demo is done).
- A prover/verifier calculus (POPL'14 style). Not ported.
- Preventing denial of service. The server can go silent; zrdt only proves it cannot *pretend*.

## 2. Decisions already made

| Decision | Rationale |
|---|---|
| Integrity theorems end in `∨ CollisionIn hash u`, with `u` the stores involved | A global "a collision exists" is provably true for any real hash (fixed output, unbounded input), which would make every theorem vacuous. `CollisionIn` names two records the replicas hold. |
| No server-assigned order; heads are the digest | Keybase's prev-pointers kept the server as ordering coordinator. Here `heads` is a function of the records, so two members with equal heads hold equal stores (`fetched_agree`). |
| Refinement to a `HashMap` implementation is non-negotiable | It is the difference between "proofs about a model" and "proofs about the code the phone runs". The rubric asks exactly this question. |
| `hash` = SHA-256 over a canonical encoding, `encode` proved injective | Keeps SHA-256 outside the proofs (a bare parameter) while making "collision" in our theorems mean a real SHA-256 collision, not an encoder bug. |
| Links travel in a new `DataMessage` field `repeated bytes zrdt_links = 200` | Unknown fields are ignored by stock clients, so forks and stock clients coexist in one group. |
| Signal-Desktop fork is primary; Android is stretch | TypeScript/Electron: one codebase, three instances on one machine, native module via N-API. |
| Villain = `EvilServer`, a subclass of Signal-Desktop's mock server **[amendment, from APP.md §8a]** | The fork's own test suite ships a mock Signal server whose single `send(target, message)` is the delivery choke point. Overriding it gives drop/delay/reorder/replay/partition in about fifty lines, needs no phone numbers, no certificate work and no rate limits, and provisions the fake phones the three desktops link to. It has exactly the real server's power (envelopes only). A TLS proxy against `chat.staging.signal.org` is the stretch (APP.md §8b). |
| Comparator only at the end (phase F) | Statements change until then. Needs `bwrap` (Linux): run in Docker. |
| `TaskList.lean` and the `_global` theorems are deleted | Grounding example from the prompt; no role in the chat. The `_global` forms prove the vacuous statement and mislead readers. |

## 3. Architecture

```
  Spec   (Lean)   Finset model: Record, Store, accept, heads, Reach, Complete, Tight, Fetched
                  theorems: fetched_agree, fetched_build, no_silent_exclusion, fetched_union, …
        │  refinement theorems (Refine.lean): abs impl = model
  Impl   (Lean)   ChatStore = Std.HashMap Digest Record + Std.HashSet Digest heads
                  accept / heads / check / merge / encodeStore / decodeStore / has / reaches
        │  lake build → C (+ Lean runtime, vendored SHA-256)
  libzrdt (C)     zrdt_* functions below; @zrdt/native (N-API) wraps them for Node/Electron
        │  FFI (bytes in, bytes/verdicts out)
  Host            Signal-Desktop fork: transport, storage of the blob, UI; EvilServer (mock server) as villain
```

The host never computes a hash, never decides acceptance, never computes heads. If the host
corrupts the stored blob, `zrdt_check` on reload catches it, exactly as a tampered server is caught.

### 3.1 Repository layout (proposed; `APP.md` may refine the host side)

```
zrdt/                          this repo (Lean, FFI, proxy, docs)
  Crdt/Merkle/Defs.lean        keep (un-private what other modules need)
  Crdt/Merkle/Integrity.lean   keep (delete _global theorems)
  Crdt/Merkle/Chat.lean        new: chat theorems
  Crdt/Merkle/Hash.lean        new: Digest, sha256 (extern), hashRecord
  Crdt/Merkle/Encode.lean      new: encode, encode_injective
  Crdt/Merkle/Impl.lean        new: ChatStore and its operations
  Crdt/Merkle/Refine.lean      new: abs, Inv, refinement theorems
  Crdt/Merkle/Ffi.lean         new: @[export zrdt_*] wrappers over ByteArray
  Test/Axioms.lean             gate (extend; remove TaskList lines)
  Test/Differential.lean       plausible: ChatStore vs Finset model
  Test/Vectors.lean            #guard vectors; `lake exe vectors` writes vectors/vectors.json
  ffi/zrdt.h ffi/sha256.c ffi/zrdt_stub.c ffi/smoke.c
  proxy/                       stretch only: TLS proxy against staging (APP.md §8b)
  vectors/vectors.json
  docs/PLAN.md docs/PLAN_HUMANS.md docs/APP.md   (plus docs/PHASE1-PROMPT.md, docs/VISIBILITY-AUDIT.md)
  README.md CLAUDE.md
signal-desktop-zrdt/           separate repo: the Signal-Desktop fork (see APP.md)
  packages/zrdt-native/        @zrdt/native (N-API package; lives in the fork so its existing
                               electron rebuild wiring builds it; vendors libzrdt.a + zrdt.h + vectors)
  demo/evil.ts demo/launch.ts  EvilServer, three Bootstraps, group, control panel (APP.md §8a)
  demo/doctor.ts               edits a store blob for beat 4
```

### 3.2 Namespaces and gate names

All spec and chat theorems live in `Crdt.Merkle`. `ChatStore` and its refinement theorems live in
`Crdt.Merkle.ChatStore`. The axiom-gate names are therefore **[amendment]**:
`Crdt.Merkle.ChatStore.check_iff_fetched`, `Crdt.Merkle.ChatStore.abs_accept`; the others are as
listed in DECISIONS under `Crdt.Merkle`.

### 3.3 C API contract (`ffi/zrdt.h`)

This is the contract the host builds against from day 1 (via the stub) and that phase C freezes.
Additions beyond DECISIONS are marked. All functions are single-threaded; a store is not shared
between threads. Byte order in all encodings is big-endian. Raw digests are 32 bytes; ACIs are 16.

```c
typedef struct zrdt_store zrdt_store;                            /* opaque */
typedef struct { uint8_t b[32]; } zrdt_digest;
typedef struct { const uint8_t *ptr; size_t len; } zrdt_bytes;   /* borrowed input */
typedef struct { uint8_t *ptr; size_t len; } zrdt_buf;           /* owned output; zrdt_free_buf */
typedef struct { zrdt_digest *ptr; size_t len; } zrdt_digests;   /* owned output; zrdt_free_digests */

int  zrdt_init(void);                        /* [addition] once per process; initialises the Lean runtime */
void zrdt_free_buf(zrdt_buf);                /* [addition] */
void zrdt_free_digests(zrdt_digests);        /* [addition] */

zrdt_digest zrdt_hash(zrdt_bytes payload, const zrdt_digest *links, size_t nlinks, const uint8_t author[16]);

zrdt_store *zrdt_store_new(void);
void        zrdt_store_free(zrdt_store *);

typedef enum { ZRDT_ACCEPTED = 0, ZRDT_MISSING = 1, ZRDT_COLLISION = 2 } zrdt_accept_status;
typedef struct { zrdt_accept_status status; zrdt_digest digest; zrdt_digests missing; } zrdt_accept_result;
zrdt_accept_result zrdt_accept(zrdt_store *, zrdt_bytes payload, const zrdt_digest *links, size_t nlinks,
                               const uint8_t author[16]);
/* ACCEPTED: record inserted (or already present: idempotent), digest = its hash, missing.len = 0.
   MISSING:  store unchanged; missing = the links that do not resolve (non-empty).
   COLLISION [amendment]: a different record with the same digest is already stored; store unchanged. */

zrdt_digests zrdt_heads(const zrdt_store *);

typedef enum { ZRDT_OK = 0, ZRDT_CHECK_MISSING = 1, ZRDT_CHECK_UNREACHABLE = 2 } zrdt_check_status;
typedef struct { zrdt_check_status status; zrdt_digest digest; } zrdt_check_result;
zrdt_check_result zrdt_check(const zrdt_store *);
/* OK iff every link of every record resolves (Complete) and every record is reachable from the heads
   (Tight). Otherwise the first offending digest: a link that resolves to nothing, or a record no head
   reaches. Deterministic: same store, same answer. */

typedef struct { zrdt_store *store; zrdt_digest collision; } zrdt_merge_result;
zrdt_merge_result zrdt_merge(const zrdt_store *a, const zrdt_store *b);
/* New store = union; inputs unchanged. store == NULL ⇒ [amendment] same digest, different records
   in a and b; `collision` names it. */

zrdt_buf    zrdt_encode(const zrdt_store *);
zrdt_store *zrdt_decode(zrdt_bytes, int *err);
/* decode is structural only (malformed ⇒ NULL, err ≠ 0; duplicate digest ⇒ NULL, err = COLLISION).
   It recomputes every digest and the heads. It does NOT run check; the host calls zrdt_check after
   every decode and treats a non-OK result as "rejected" (demo beat 4). */

int zrdt_has(const zrdt_store *, zrdt_digest);
int zrdt_reaches(const zrdt_store *, zrdt_digest from, zrdt_digest to);  /* "seen by" */
int zrdt_get(const zrdt_store *, zrdt_digest, zrdt_buf *payload, zrdt_digests *links, uint8_t author[16]);
/* [addition] needed to answer ZrdtResendRequest by digest. */
```

Why `COLLISION` exists at this layer **[amendment]**: the map is keyed by digest, so the
implementation cannot hold two different records with one digest. The model's `accept` would
insert both. The refinement therefore says: on `ACCEPTED`, `abs` tracks the model; on `COLLISION`,
`CollisionIn hashRecord (insert r (abs c))` holds, which is exactly the disjunct in every integrity
theorem, now observed at run time at the one place it is observable.

### 3.4 Encodings (shared by Lean `encode`, the stub, the native module and the vectors)

- **Record** (`Encode.lean`, hashed by `hashRecord`):
  `"zrdt1" ‖ u32 len(payload) ‖ payload ‖ u32 nlinks ‖ links sorted ascending bytewise, deduplicated ‖ author(16)`.
  `encode_injective` is proved over this format. Sorting makes link order irrelevant to the hash.
- **Payload** (built by the host; opaque bytes to Lean):
  `u64 senderTimestamp ‖ u32 len(body) ‖ body (UTF-8 bytes as sent) ‖ u32 natt ‖ attachment digests (32 each, in order)`.
  Phase C may export `zrdt_payload(...)` **[addition, optional]** so the host does not hand-roll it.
- **Store blob** (`encodeStore`): `"zrdtS1" ‖ u32 count ‖ (u32 len ‖ encode(record))* ` sorted by digest.
  `decode_encode` is proved. Heads are not stored; decode recomputes them.
- **Digest in protobuf**: raw 32 bytes. **Short code in UI**: see `APP.md`; comparison codes ≥ 80 bits.

### 3.5 Record mapping (Signal)

payload = canonical bytes of (sender timestamp, text body, attachment digests); links = the sender's
heads at send time; author = sender ACI. Links travel in `DataMessage.zrdt_links = 200`. Recovery:
`ZrdtResendRequest { repeated bytes digests = 1 }` / `ZrdtResend { bytes record = 1; bytes
dataMessage = 2; bytes authorAci = 3 }`, both at `Content` level (tags 200/201) so stock clients
ignore them **[amendment, from APP.md §3]**, so any member re-sends a record by digest, modelled on
Signal's retry-receipt flow. Detail in `APP.md`.

## 4. Work breakdown

Effort is in agent-days of one continuously working agent. Lanes run in parallel in separate git
worktrees (§5). The lead merges serially.

### Phase A — Lean spec cleanup + `Chat.lean` (lane L1, 0.5–1 day, no dependencies)

Deliverables:
- Delete `Crdt/Merkle/TaskList.lean`, its import in `Crdt.lean`, its three gate lines in
  `Test/Axioms.lean` (`add_wins`, `fetched_live_agree`, `remove_requires_closure`).
- Delete the seven `*_global` theorems in `Integrity.lean` and `Collision` / `CollisionIn.global`
  in `Defs.lean`. Remove `private` from `digests_union`, `digests_empty`, `mem_heads`, and the `Toy`
  namespace (other modules and tests need them). Fix the line-length drift (≤ 100 chars).
- `Crdt/Merkle/Chat.lean`, namespace `Crdt.Merkle`, each with docstring + concrete example:
  - `no_silent_exclusion : Complete hash s hs → m ∈ t → Reach hash t hs (hash m) →
    m ∈ s ∨ CollisionIn hash (s ∪ t)` (if another member holds a message that lies behind your
    heads, you hold it too, or your copy fails the check; the statement in `PLAN_HUMANS.md` §4(2)),
    `holds_past : Closed hash s → r ∈ s → Complete hash s r.links` (holding a record means holding
    everything its sender had seen), and `accept_rejects_names_missing : r ∉ s →
    accept hash s r = s → ∃ d ∈ r.links, d ∉ digests hash s` (a rejection names a missing link).
  - `fetched_union : Fetched hash s hs → Fetched hash t ht → Fetched hash (s ∪ t) (hs ∪ ht)`
    **[amendment: no collision clause; it is not needed]** and
    `heads_union_subset : heads hash (s ∪ t) ⊆ heads hash s ∪ heads hash t`.
  - `Equivocation s a b : Prop` (both in `s`, `a ≠ b`, same `author`, same `links`), decidable, and
    `fork_visible : Equivocation (s ∪ t) a b → hash a ≠ hash b ∨ CollisionIn hash (s ∪ t)`, plus
    `equivocation_union : a ∈ s → b ∈ t → a ≠ b → a.author = b.author → a.links = b.links →
    Equivocation (s ∪ t) a b`.
  - `withheld_tail_undetectable`: a countermodel. Two concrete stores over `Toy`, both `Fetched`
    from their own heads, one a strict subset of the other, with `¬ CollisionIn` on the union. This
    is the `¬ Spec bad`-style statement: the check alone cannot see a withheld tail.
  - `buildRetry hash l` (fuel = `l.length` passes of `accept` over the pending list),
    `AcceptBuilt hash s := ∃ l, l.toFinset = s ∧ build hash l = s`, and
    `build_retry_eq_union : AcceptBuilt hash s → AcceptBuilt hash t → l.toFinset = s ∪ t →
    buildRetry hash l = s ∪ t` **[amendment: stated via `AcceptBuilt`, since a `Closed` set with a
    hash cycle is never accepted; see §7]**. Corollary: `buildRetry` output is `Fetched` from its
    own heads or has a collision (from `fetched_build`).
- Gate lines for `no_silent_exclusion`, `fetched_union`, `fork_visible`.

Done when: `lake build` succeeds with no `sorry` warnings; `lake exe axiom_check` prints
`axiom gate passed`; every new theorem shows `[propext, Classical.choice, Quot.sound]` or fewer;
`grep -rn "sorry\|admit\|native_decide" Crdt/Merkle` is empty; every main theorem has a concrete
instance with hypotheses discharged.

### Phase B — Implementation + refinement (lane L2, 2–4 days; the core verification deliverable)

Order inside the lane: `Hash.lean` → `Encode.lean` → `Impl.lean` (compiling, `#eval`-able) →
publish the `ChatStore` signatures to lane L3 → `Refine.lean`.

Deliverables:
- `Hash.lean`: `Digest` (32 bytes with a size proof; `DecidableEq`, `Hashable`, `Ord`, `LawfulBEq`),
  `Aci` (16 bytes), `opaque sha256 : ByteArray → Digest` with `@[extern "zrdt_sha256"]`,
  `hashRecord r := sha256 (encode r)`. `Record ByteArray Digest Aci` must have `DecidableEq`.
- `Encode.lean`: `encode` per §3.4; `encode_injective : Function.Injective encode`; `#guard`
  vectors.
- `Impl.lean`, namespace `Crdt.Merkle.ChatStore`: `structure ChatStore` (`map`, `heads`);
  `accept : ChatStore → Record → AcceptResult × ChatStore` with
  `inductive AcceptResult | accepted (d : Digest) | missing (ds : List Digest) | collision (d : Digest)`;
  `heads`; `check : ChatStore → CheckResult` (`| ok | missing d | unreachable d`) as a worklist
  traversal with `termination_by` (fuel = map size is acceptable); `merge` (returns
  `Except Digest ChatStore`); `encodeStore` / `decodeStore`; `has`; `reaches`. Everything
  computable: `#eval` each.
- `Refine.lean`: `abs : ChatStore → Store ByteArray Digest Aci` (the finset of the map's values);
  `Inv c := (∀ d r, c.map[d]? = some r → hashRecord r = d) ∧ c.heads.toFinset = heads hashRecord (abs c)`;
  theorems `inv_new`, `abs_accept` (on `accepted`: `abs c' = accept hashRecord (abs c) r ∧ Inv c'`;
  on `missing ds`: `c' = c ∧ ds ≠ [] ∧ ∀ d ∈ ds, d ∈ r.links ∧ d ∉ digests hashRecord (abs c)`;
  on `collision d`: `c' = c ∧ CollisionIn hashRecord (insert r (abs c))`), `heads_eq`,
  `check_iff_fetched : Inv c → (c.check = .ok ↔ Fetched hashRecord (abs c) (heads hashRecord (abs c)))`,
  `check_missing_sound`, `check_unreachable_sound` (the named digest really is the failing one),
  `abs_merge`, `decode_encode : Inv c → decodeStore (encodeStore c) = .ok c`, `inv_decode`,
  `reaches_iff : Inv c → (c.reaches a b ↔ Reach hashRecord (abs c) {a} b)` (needed for "seen by").
- `Test/Differential.lean`: `plausible` properties comparing `ChatStore` to the finset model on
  random record lists (generator draws links from digests of earlier records so links sometimes
  resolve): `abs (buildImpl l) = build hashRecord l`, heads agree, `check` agrees with a naive
  reference `checkRef` on finsets, `decodeStore ∘ encodeStore = id`. Run these *before* proving.
- Gate lines for `check_iff_fetched`, `abs_accept`, `encode_injective`.

Done when: all of the above build with no `sorry`; gate passes; `lake build` has no new warnings;
`#eval` of each operation on the `Toy` scenario matches the model; differential tests pass.

### Phase C — FFI, libzrdt, vectors, differential harness (lane L3, 1–2 days; needs B's signatures)

Deliverables:
- `Ffi.lean`: `@[export zrdt_...]` functions over `ByteArray` implementing §3.3 (store handles as
  Lean objects behind `lean_object*`; the C side wraps them in `zrdt_store`).
- `ffi/zrdt.h`, `ffi/sha256.c` (vendored single file, public domain or BSD), `ffi/smoke.c`.
- Build: `make lib` → `build/libzrdt.a` (Lake static facet of the `Crdt` lib + runtime; link via
  `leanc`). `make vectors` → `vectors/vectors.json` from `lake exe vectors` (`Test/Vectors.lean`
  `main`). Record the exact link line in `APP.md`.
- `@zrdt/native` (in the fork at `packages/zrdt-native/`, APP.md §2): N-API module exposing the
  API with `Buffer`s, built by the fork's existing `electron:install-app-deps` wiring; a Node test
  runs `vectors.json` through the native module and through the independent reimplementation (the
  upgraded stub, §4 D) and diffs. This repo ships `build/libzrdt.a`, `ffi/zrdt.h` and
  `vectors/vectors.json`; the fork vendors them under `packages/zrdt-native/prebuilt/`.
- `ffi/zrdt_stub.c`: day-1 stub (handed to lane H1 before Lean impl exists). Day 1: trivial
  (accept everything, `check` ok, `hash` = SHA-256 of the record encoding). By end of phase D:
  upgraded to a naive, unverified C implementation of the same semantics, which is then the
  "independent reimplementation" for the host-side differential test.

Done when: `make lib && make vectors` succeed on macOS and Linux; `smoke.c` links and passes all
vectors; the native module loads in the fork's Electron and passes the same vectors.

### Phase D — Signal-Desktop fork (lanes H1 transport/native, H2 UI; 3–5 days; starts day 1 vs stub)

See `APP.md` for the detail. Deliverables in brief:
- Proto: `DataMessage.zrdt_links = 200`; `ZrdtResendRequest`, `ZrdtResend` content types.
- Send path: build payload, read heads from the store, attach links, `zrdt_accept` own record.
- Receive path: build record from the `DataMessage`, `zrdt_accept`; on `MISSING`, show the gap
  placeholder and send `ZrdtResendRequest` (first to the server's queue by waiting, then to peers);
  on `ZrdtResend`, accept the record; answer resend requests from `zrdt_get`.
- Storage: one blob per group in the existing SQLite DB; `zrdt_decode` + `zrdt_check` on load.
- UI states: per-message code (tap); gap placeholder; compare screen with the four outcomes
  (identical / they're behind / you're behind / withheld, with digest); rejected banner;
  checkpoint message with "seen by" from `zrdt_reaches`; fork marker.
- Launch: `demo/launch.ts` brings up one `EvilServer`, three `Bootstrap`s sharing it, a group, and
  three desktops with separate profiles, injecting config through `SIGNAL_CI_CONFIG` (APP.md §8a).
  No accounts, no certificate work.

Done when: three instances against the evil server with all rules off behave like stock Signal,
and a stock desktop in the group ignores the field; all UI
states reachable with the stub's naive implementation; then the stub swapped for `@zrdt/native`
with no host code change (the API is the contract).

### Phase E — Villain (lane H3, 0.5–1 day; starts day 1)

`EvilServer extends Server` from `@signalapp/mock-server`, in the fork at `demo/evil.ts`: override
`send(target, message)` with a rule list (`dropNextTo(member)`, `delay(member, ms)`,
`reorder(member)`, `replay(member)`, `partition(set)`), a tiny control panel (HTTP `/rules`, `/log`)
or REPL, and `demo/launch.ts` (three `Bootstrap`s sharing the server, `createGroup`, `link()` each
desktop). Detail and verified file references in `APP.md` §8a. The server issues sealed-sender
certificates and sees envelope framing and timing only, so "drop Alice's message to Carol" is
operated as "drop the next envelope to Carol" with the operator timing Alice's send.

Done when: each rule demonstrably changes what a fork receives; with all rules off, three stock
desktops through the same server behave normally; the launch script runs from cold in one command.

Stretch, only after beats 1–4 pass: a TLS-terminating proxy in front of `chat.staging.signal.org`
with the same rule set, for a demo against the real network (`proxy/`; APP.md §8b, including the
open question whether libsignal-net honours a custom `certificateAuthority`).

### Phase F — Demo assembly, README, Comparator, docs (1–2 days; depends on all)

- Rehearse the four beats (§8) twice from cold start; write `DEMO.md` with the exact clicks.
- README: what is proved (capstones in plain English), trusted base (Lean compiler/runtime, C
  compiler, SHA-256, FFI glue, host passing bytes faithfully, Signal for attribution and
  confidentiality), what is not proved (§1 non-goals), the sourced comparison with Signal, MLS and
  Keybase (from `PLAN_HUMANS.md`).
- Comparator: `Comparator/Challenge.lean` with the capstone statements and `sorry` bodies;
  `comparator.json` per `lake help comparator` (permitted axioms: `propext`, `Classical.choice`,
  `Quot.sound`); `make comparator` runs `lake comparator` inside a Linux Docker image with `bwrap`;
  also `lake check`. Both must pass.
- Keep `PLAN.md`, `PLAN_HUMANS.md`, `APP.md` current; the lead updates §10 at each merge.

### Critical path and parallelism

```
day 1:  A.cleanup ─┐
        E.villain  │ (parallel from day 1)
        D.transport│ against ffi/zrdt_stub.c
        D.ui       │
        B.Hash+Encode+Impl ──► C.Ffi+lib+native ──► D.swap stub→native ──► F.demo
                   └──► B.Refine (longest single task; runs beside C and D)
```

Critical path ≈ B.Impl (1d) → C (1–2d) → D.swap (0.5d) → F (1–2d), with B.Refine (2d) and
D.ui (3–4d) running alongside. If B.Refine slips, the demo still ships on the unproved impl, and
the README says exactly which refinement theorems are missing. Never ship a `sorry` to make it look
proved.

### Agent roster and file ownership (disjoint; no two agents edit one file)

| Agent | Owns | Lane |
|---|---|---|
| lean-spec | `Defs.lean`, `Integrity.lean`, `Chat.lean`, gate lines for A | L1 |
| lean-impl | `Hash.lean`, `Encode.lean`, `Impl.lean`, `Test/Vectors.lean` | L2 |
| lean-refine | `Refine.lean`, `Test/Differential.lean`, gate lines for B | L2 (after Impl compiles) |
| ffi | `Ffi.lean`, `ffi/*`, fork `packages/zrdt-native/*`, Makefile `lib`/`vectors`, lakefile changes | L3 |
| desktop-transport | fork: proto, send/receive, storage, native module wiring | H1 |
| desktop-ui | fork: components, screens, codes | H2 |
| villain | fork `demo/*` (EvilServer, launch, doctor); `proxy/*` only for the stretch | H3 |
| docs-demo | `README.md`, `DEMO.md`, `Comparator/*`, `make comparator` | F |

The lead: merges serially, approves statement changes, keeps §10 current, reruns the gate after
every merge.

## 5. Rules for agents

From `CLAUDE.md`, restated as hard rules:

1. **One `lake` process per checkout.** Never two `lake` invocations, or `lake` plus a REPL, in one
   worktree at once. Parallel Lean agents each work in their own git worktree
   (`git worktree add ../zrdt-<agent> -b <agent>/<topic>`), run `lake exe cache get` there, and
   never symlink another worktree's `.lake`.
2. **Build one module per edit**: `lake build Crdt.Merkle.<Module>`. Full `lake build` at
   checkpoints. Read the warnings: a successful build can still contain `sorry`.
3. **Forbidden**: `sorry`, `admit`, `native_decide`, new `axiom`s, `debug.skipKernelTC`,
   `implemented_by`/`unsafe` that changes meaning, `maxHeartbeats 0`. Raise `maxHeartbeats` only
   on the one declaration that needs it, with a comment.
4. **Statements are the contract.** Never weaken a theorem, change a definition the spec depends
   on, or prove a theorem about a copy of the code. If a statement resists: test it with
   `plausible` or a counterexample, report, and propose an amendment to the lead. Statement changes
   require lead approval and get a **[amendment]** note in this file.
5. **Specs people can review**: plain English, a docstring and a concrete example per definition;
   every main theorem instantiated on a concrete input with every hypothesis discharged; at least
   one `¬ Spec bad` example per spec; no unnecessary math vocabulary.
6. **`#print axioms` on every change** (the gate does this for listed theorems; check unlisted ones
   by hand). Allowed: `propext`, `Classical.choice`, `Quot.sound`. Nothing else, ever.
7. **Executable definitions stay computable.** No `Classical` in data; `#eval` everything the
   library exports. `Decidable` instances so `decide`/`#guard` work on small examples.
8. **Skeleton first**: state definitions and theorems with `sorry`, check the capstone follows
   from its lemmas, then fill one at a time. Lemmas over unfolding; never `simp` through generated
   or monadic code.
9. **Never edit generated files** (protobuf outputs, `vectors.json`): regenerate them.
10. **Git**: stage only files you touched; the lead merges serially; commit messages end with
    `Co-Authored-By: Claude Fable 5.1 <noreply@anthropic.com>`. Do not commit `.lake`.
11. **Report faithfully**: failed builds, skipped steps, and anything unusual go in the hand-back,
    in the first line.

## 6. Gates and verification ladder

Run bottom to top; each rung assumes the one below passed.

| Rung | Command | Pass condition |
|---|---|---|
| 1 | `lake build Crdt.Merkle.<Module>` | no errors, no `sorry` warnings for that module |
| 2 | `lake build` | "Build completed successfully", no new warnings |
| 3 | `lake exe axiom_check` | prints `axiom gate passed: all checks pinned by #guard_msgs at compile time` |
| 4 | fresh clone: `make install && make run` | both succeed with no manual steps |
| 5 | `lake build Test.Differential` | all `plausible` properties pass (B onward) |
| 6 | `make lib && make vectors && cc ffi/smoke.c -o smoke … && ./smoke` | all vectors pass through libzrdt (C onward) |
| 7 | `cd native && npm test` | native module == independent reimplementation on `vectors.json` (C/D) |
| 8 | end-to-end: three forks + evil server, `DEMO.md` beats 1–4 | each beat's on-screen criterion (§8) met |
| 9 | `make comparator` (Docker, Linux, `bwrap`) and `lake check` | both exit 0 (phase F only) |

Trusted at rung 9: Lean kernel (plus external checkers with `--paranoid` if time), the statements
in `Comparator/Challenge.lean`. Everything below the spec is covered by refinement; everything
below Lean (compiler, runtime, C, SHA-256, FFI, host) is listed in the README as trusted.

## 7. Risk register

| Risk | Impact | Mitigation / fallback |
|---|---|---|
| Lean→C link: runtime init (`lean_initialize_runtime_module`, module initialiser, `lean_io_mark_end_initialization`), `leanc` flags, static facet on macOS arm64 vs Linux | blocks C, D.swap | Day-1 spike: export one function, call it from a C `main` and from Node. Record the exact link line in `APP.md`. Keep Linux (Docker) as the reference build. |
| Vendored C via Lake needs an `extern_lib` target (likely `lakefile.lean`, not toml) | blocks `#guard`/`#eval` of `sha256` in the interpreter | `lake translate-config` to `lakefile.lean` if required. Fallback: pure-Lean SHA-256 (compiled `UInt32` ops are native; checked against NIST vectors with `#guard`); it also removes SHA-256 from the trusted base. Decide in week 1 (§9). |
| `Std.HashMap` lemma coverage in v4.35 makes `Refine.lean` slow going | B.Refine slips | Keep `Inv` minimal; prove through `Std.HashMap` lemmas (`getElem?_insert`, `mem_insert`, `toList`). Fallback: `Std.TreeMap` keyed by digest bytes with its lemma library; performance is still fine for chat sizes. |
| Hash cycles in the model (a record linking its own digest) break naive statements | wrong theorem shapes | Already handled: `fetched_union` is stated on head sets, `build_retry_eq_union` via `AcceptBuilt`, "fetched from own heads" only for accept-built stores (`fetched_build`). Do not try to prove `Fetched s hs → Fetched s (heads s)`: it is false (two-record cycle). |
| Signal-Desktop: build time (alpha `main`, Electron 45), multi-instance | D slips | Pin to the latest tagged release; the mock-server launch gives separate temp profiles and fake primaries, so no accounts are needed; start the fork build on day 1 before any code changes. |
| Mock-server fidelity: groups v2, sender keys, `ciMode` side effects on the UI | E, D | Verify on day 1 that `ts/test-mock` already exercises group creation and sender-key sends through the mock server; try `ciMode: false`; if a needed server feature is missing, add it to the mock (plain TypeScript) rather than switching villain. |
| Electron native module ABI | D.swap blocked | Build `@zrdt/native` with `electron-rebuild` against the fork's Electron version on day 1 using the stub, so only the `.a` changes later. |
| Sealed sender: the server cannot see who sent an envelope | demo beat 2/3 harder | Operate drops as "next envelope to Carol"; rehearse timing. (Certificate pinning and upstream acks only matter for the proxy stretch, APP.md §8b.) |
| Time | everything | **Hard fallback**: if the Signal-Desktop fork stalls by mid-project, build a minimal Electron chat client (same `@zrdt/native`, same UI states) over plaintext JSON through the same `EvilServer` rule engine. The Lean deliverable, the native module, the villain and the four beats survive unchanged; only "on top of Signal" is lost. Decide at the mid-point checkpoint. |
| Over-claiming | credibility | README and demo say "detect", never "prevent"; never claim attribution or confidentiality; cite Keybase as prior art. |

## 8. Demo acceptance criteria

Three desktop instances (Alice, Bob, Carol) against one `EvilServer` with a visible control panel,
one group.

1. **Codes match.** Alice, Bob, Carol exchange three messages. On each screen, tapping the last
   message shows the same code; the compare screen says "identical". Visible: the three codes side
   by side, equal.
2. **Gap.** Server: drop the next envelope to Carol; Alice sends; Bob replies.
   Carol's screen shows a placeholder *above* Bob's reply: "1 message you haven't received. Bob
   replied to it." Carol's app sends `ZrdtResendRequest`; Bob's app answers; the placeholder is
   replaced by Alice's message, with the same code Alice and Bob see. Visible: the placeholder
   appearing, then resolving, with no manual action.
3. **Withheld tail.** Server: drop the next envelope to Carol; Alice sends; nobody
   replies. Carol's screen shows nothing wrong (and the demo says so: that is the theorem
   `withheld_tail_undetectable`). Carol opens compare-with-Bob: her app says "Bob has a message the
   server won't give you: ·k7f2". Visible: the withheld digest named on Carol's screen.
4. **Doctored restore.** Carol's store blob is edited on disk (one record removed, or one byte
   changed). Carol restarts. Visible: a red banner "This copy of the chat was altered: ·9ac1 is
   missing", and the chat refuses to load that blob.

Each beat ≤ 60 seconds; the whole demo ≤ 5 minutes; a stock Signal client in the same group keeps
working throughout (shown once, briefly).

## 9. Open questions for the humans

1. **Deadline** and judging date; this sets the mid-point checkpoint for the fallback decision.
2. **Signal accounts**: none are needed for the mock-server demo. For the proxy stretch against
   staging: who provides three numbers?
3. **Android**: attempt it at all? (Recommendation: no, unless desktop beats 1–4 pass with two days
   to spare.)
4. **SHA-256**: vendored single-file C (DECISIONS), OpenSSL from the system, or pure Lean? Pure Lean
   shrinks the trusted base and avoids `extern_lib`; C is faster and conventional.
5. **Lean version**: stay on v4.35.0 / Mathlib v4.35.0 for the whole project (recommended; a bump
   risks `Std.HashMap` lemma renames mid-refinement).
6. **Comparator**: is a Docker-based run acceptable to the judges, or do they run it themselves on
   Linux? Either way the challenge file is the deliverable.
7. **Fork repo**: name and hosting for `signal-desktop-zrdt` (public fork of signalapp/Signal-Desktop).

## 10. Status snapshot (2026-10-31)

**Exists and builds** (`lake build` clean, `make run` prints `axiom gate passed`; all listed
theorems depend only on `[propext, Classical.choice, Quot.sound]`):

- `Crdt/Merkle/Defs.lean`: `Record`, `Store`, `CollisionIn`, `digests`, `Closed`, `heads`, `Reach`,
  `Complete`, `Tight`, `Fetched`, `accept`, `build`, `Receipt`/`receipt`; proved `CollisionIn.of_mem`,
  `CollisionIn.mono`, `mem_digests`, `digests_union`, `digests_empty`, `closed_empty`,
  `closed_union`, `mem_heads`, `heads_subset_digests`, `complete_of_closed`, `Reach.mem_of_bound`,
  `Reach.lift`, `accept_of_resolves`, `closed_accept`, `closed_build`, `heads_insert`,
  `heads_insert_of_links_heads`, `receipt_heads_sound`, `receipt_confirms`, `merge_eq_union`,
  `strong_eventual_consistency`, `eventual_agreement`. Also `Collision` and `CollisionIn.global`
  (to delete in A).
- `Crdt/Merkle/Integrity.lean`: proved `accept_unique`, `subset_of_digests_subset`,
  `eq_of_digests_eq`, `reach_mono_of_complete`, `subset_of_fetched`, `fetched_agree`,
  `merge_fetched`, `fetched_accept`, `fetched_build`; plus seven `*_global` forms (to delete in A).
- `Crdt/Merkle/TaskList.lean`: proved task-list theorems and a scenario (to delete in A).
- `Test/Axioms.lean`: eight Merkle gate lines (`accept_unique`, `fetched_agree`, `merge_fetched`,
  `fetched_build`, `heads_insert`, `TaskList.add_wins`, `TaskList.fetched_live_agree`,
  `TaskList.remove_requires_closure`); the last three go in A.
- `README.md`: phase 1 write-up (to be rewritten for the chat in F).
- Scratch only (not in repo): `TimeOrdered`, `time_le_of_reach`, `time_between` (timestamps; parked,
  out of scope).

**Unwritten**: `Chat.lean`, `Hash.lean`, `Encode.lean`, `Impl.lean`, `Refine.lean`, `Ffi.lean`,
`Test/Differential.lean`, `Test/Vectors.lean`, `ffi/*`, the fork (with `packages/zrdt-native/*` and
`demo/*`), `proxy/*` (stretch), `Comparator/*`, `DEMO.md`.

**Git state** (uncommitted; the lead should commit phase 1 as-is before phase A starts, so the
deletions are reviewable):

- `?? Crdt/Merkle/` (Defs, Integrity, TaskList), `?? README.md`, `?? docs/`, ` M Crdt.lean`,
  ` M Test/Axioms.lean`: this session's work.
- ` M Makefile`, ` M .gitignore`: changed by another editor during the session (adds a `help`
  default target and a `make graph` import-graph target; ignores `docs/imports.*`). `make install`
  and `make run` still work. Keep.
- Another editor also, during the session: made `Toy` and several `Defs.lean` theorems
  (`digests_union`, `digests_empty`, `mem_heads`) `private`; made `Crdt/Convergence.lean`'s
  `converged_states_agree` `private`; changed `Crdt/ORSet.lean` (not inspected); restructured parts
  of `TaskList.lean`. Phase A reverses the `private` changes that other modules need and deletes
  `TaskList.lean`; the lead should confirm no phase 0 statement changed (`git diff Crdt/*.lean`).
