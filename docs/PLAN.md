# zrdt — project plan (for the lead agent)

Status date: 2026-11-01. Audience: the AI lead coordinating the work, and the agents it dispatches.
Ground truth for names, files, API and phases is the DECISIONS block this plan was derived from.
Where this plan amends it, the change is marked **[amendment]**. A marker on a heading covers the
whole section.
Review of 2026-11-01: `docs/review-2026-11-01/` (`REVIEW.md`, `UPDATE-690ae65.md`, `AMENDMENTS.md`).
`AMENDMENTS.md` (A1–A13) is the source of every name the review adds, and the user approved its
amendments. Any other **[amendment]** needs the lead's sign-off; the few added after
`AMENDMENTS.md` say "(lead to confirm)".
Sibling documents: `PLAN_HUMANS.md` (the theorems and design in plain English), `APP.md`
(Signal-Desktop integration detail) and `RESTORE_PLAN.md` (restore from any peer's dump, confirmed
by live messages). This file owns scope, contracts, phases, gates and rules.

## 1. Goal

**Pitch:** a verified transcript-consistency layer for Signal group chats. Each message carries
hash links to the messages its sender had seen, and a verified Lean core checks them.
**[amendment]**

> A server cannot make a member's app accept a history with a hole in it: if any later message
> builds on one you lack, you are told, and your app asks for it. Two members can confirm with
> one code that they hold the same set of messages; once the server splits a group it can never
> merge it back without the gap showing. The server can still delay, hold back the newest
> messages until someone replies or members compare, and deliver concurrent messages in
> different orders.

Signal provides confidentiality and sender authentication. zrdt provides completeness and
consistency of the history. The core is written in Lean without Mathlib, proved in Lean with
Mathlib, and compiled to a small program, `zrdtd`, that runs beside a Signal-Desktop fork and
checks every record the fork sends or receives. Attacks are shown live against an "evil server":
Signal-Desktop's own mock Signal server (`packages/mock-server`, used by its integration tests)
with its delivery hooks overridden. **[amendment]** A TLS proxy in front of Signal's staging
server is the stretch for a demo against the real network. Judging (rules.md) rewards an
important property proved about the code itself, plus a demo a non-technical person understands.
Both are required; neither alone is enough.

**Non-goals** (say so in the README; never claim them):

- Signatures inside records. Signal authenticates the sender of each live message. A record that
  arrives relayed or imported counts as its author's only once `authorConfirmed` holds (§3.5), and
  that needs the author's client to disown records in its name that it did not create.
  **[amendment]**
- Confidentiality (Signal's job). Live zrdt data rides inside Signal's encryption, but an exported
  dump leaves it. The store keeps the DAG metadata (authors, causal shape, count) of expired and
  deleted messages. Links are receipts that the whole group sees. **[amendment]**
- Open membership, key revocation, or any defence against strangers.
- Membership changes after zrdt genesis. The demo group is static. **[amendment]**
- Edits, deletes, reactions, polls, pins, timer, profile and group changes: they are not records.
  1:1 chats and Note-to-self are out. **[amendment]**
- Proving who is at fault. A gap or a "withheld" result shows that two members' histories differ.
  A member who links a made-up digest, or an author who is offline, looks the same as a server
  that drops messages. **[amendment]**
- Timestamps, anchors, or any statement about real time.
- Compaction / bounded storage (history only grows).
- Signal-Android (stretch only, after the desktop demo is done).
- A prover/verifier calculus (POPL'14 style). Not ported.
- Preventing denial of service. The server can go silent, or hold back the newest messages until
  someone replies or members compare; zrdt cannot force delivery. **[amendment]**

## 2. Decisions already made

| Decision | Rationale |
|---|---|
| Integrity theorems end in `∨ CollisionIn hash u`, with `u` the stores involved | A global "a collision exists" is provably true for any real hash (fixed output, unbounded input), which would make every theorem vacuous. `CollisionIn` names two records the replicas hold. |
| No server-assigned order; heads are the digest | Keybase's prev-pointers kept the server as ordering coordinator. Here `heads` is a function of the records, so two members with equal heads hold equal stores (`fetched_agree`). |
| Refinement to the executable store (`Std.ExtTreeMap`) is non-negotiable **[amendment]** | It is the difference between "proofs about a model" and "proofs about the code the phone runs". The rubric asks exactly this question. The map is extensional, so `=` on two stores compares their contents. |
| `hash` = SHA-256 over a canonical encoding, `encode` proved injective; SHA-256 is pure Lean **[amendment]** | In the spec the hash is a parameter, and `encode_injective` makes "collision" in our theorems mean a real SHA-256 collision, not an encoder bug. The pure-Lean SHA-256 (`Zrdt/Sha256.lean`, about 70 lines, NIST vectors as `#guard`) runs under `#eval` and `decide +kernel`. There is no `@[extern]`, no `opaque` and no C to trust. |
| zrdt data travels in a new `DataMessage` sub-message, `optional ZrdtMeta zrdt = 200` **[amendment]** | An optional sub-message is sent even when it is empty. An empty `repeated bytes` field is invisible on the wire, so a fork's first message (no heads yet) could not be told apart from a stock one. Stock clients ignore the unknown field. |
| Signal-Desktop fork is primary; Android is stretch **[amendment]** | TypeScript/Electron: one codebase, four instances on one machine. The Lean code runs beside it as `zrdtd` (below). |
| Villain = `EvilServer`, a subclass of Signal-Desktop's mock server that overrides `handleMessage` and `prepareMultiDeviceMessage` **[amendment]** | The fork's own test suite ships a mock Signal server. Every delivery to a linked desktop goes through `handleMessage`, and `prepareMultiDeviceMessage` shows the recipient set. Overriding them (not `send()`, which also carries the fake phones' own traffic and does not show the sender) gives `dropGroupMsg`, `blackhole` and `hold`/`release` with no phone numbers, no certificate work and no rate limits. The mock holds every key, so "real server power" is a policy the rules follow: they use envelopes, recipient sets and timing only. A TLS proxy against `chat.staging.signal.org` is the stretch (APP.md §8b). |
| Comparator only at the end (phase F) | Statements change until then. Needs `bwrap` (Linux): run in Docker. |
| `TaskList.lean` and the `_global` theorems are deleted | Grounding example from the prompt; no role in the chat. The `_global` forms prove the vacuous statement and mislead readers. |
| The checked store is a type: `CheckedStore` = raw store + certificate, both without Mathlib **[amendment]** | No unchecked store can exist in the code or the host. `Built` holds by construction: `empty` and `accept` are the constructors, and `merge`, `open` and `salvage` insert only through the checked `accept` (one worklist, `acceptAll`). `zrdtd`'s table holds `CheckedStore` values, so every handle is checked by its type in the shipped code. Proof fields are erased, so the compiled code is the same as without them. |
| The certificate is "accept-built", not "fetched from own heads" **[amendment]** | Fetched-from-own-heads is not closed under union in the model (two records linking each other). "Some order accepted every record" is closed under accept, merge and salvage, excludes cycles by construction, and implies fetched-from-own-heads or a collision (`fetched_build`). |
| Only meaningful theorems are advertised and gated, and they are stated over `CheckedStore` **[amendment]** | The README and the gate pin the `Api.lean` statements (§3.2), which are about the type that runs. The spec theorems (`fetched_agree`, `fetched_build`, `fetched_union`, `salvage_maximal`, `confirmed_exact`, `authorConfirmed_sound`, …) are their proof obligations. Four limit examples say what links cannot do. One-line restatements (`no_silent_exclusion`, `fork_visible`, receipts, `merge_fetched`, …) are lemmas or deleted. |
| The chat id is inside the hashed record **[amendment]** | A record from another chat, resent or imported, is rejected on arrival; "belongs to this chat" is something the hash proves. |
| Resend requests go 1:1 to the referencing sender first; any holder may relay; the author's re-send gives attribution **[amendment]** | An honest sender holds what it linked at send time (`heads_subset_digests`), so one request usually gets one reply. Group broadcast is the fallback; replies are always 1:1. A relayed record is checked by `HASH` and `COMMIT` and shown "relayed by X". The author fast path re-sends the original through Desktop's sendLog, so it arrives `live` and is author-confirmed at once. |
| Two Lean packages: `core/` (`zrdt-core`) holds the code, the root (`zrdt`) holds the proofs **[amendment]** | `core/` has library `Zrdt` and exe `zrdtd`, imports only `Init` and `Std`, and has no `require`. The root keeps `Crdt` (Mathlib) and `require`s `zrdt-core` by path. A Mathlib import in compiled code would initialise and link all of Mathlib and the Lean compiler (review §1.1). Theorems about `Zrdt` definitions live in `Crdt`; that is still proofs about the code. |
| `zrdtd`, a separate process, replaces the in-process N-API module **[amendment]** | The shipped Linux Lean runtime cannot be linked into a `.node` (review §1.2). A separate process keeps Lean crashes out of Signal's window and fails closed, and needs no hand-written C. It costs little: every call site is already async. An in-process `.node` is an optional macOS stretch. |
| The record is chat id, salted commitment, canonical links and author **[amendment]** | The commitment covers the DataMessage wire bytes and a random nonce, so it commits to everything the user sees, and the store keeps no plaintext. Content stays in Desktop and follows its delete and expiry rules. With fixed-size fields and one array of fixed-size elements, `encode_injective` holds with no size bound. |
| Provenance has three values (`live`, `relayed(by)`, `imported`); attribution needs `authorConfirmed`; authors disown **[amendment]** | Hash links show that the member who linked a record holds it, not that its claimed author wrote it. Only `live` records count as an author's own. A member never refuses a record in its own name (that would stall everything that links it): it accepts it, alarms locally, and lists it in `disown` in every later message, because only `disown` lists that arrive live count (§3.5) (lead to confirm). |
| A dump is structure plus openings, under privacy rules **[amendment]** | A dump leaves Signal's encryption. It carries no content of disappearing, deleted-for-everyone or view-once messages; a member who joined later gets structure only; export needs OS authentication and a "do not share" warning. Imported and salvaged records start `imported`. |
| The fork is pinned at Signal-Desktop `v8.33.0` and is built and run on the Mac mini **[amendment]** | `zrdtd` is built there too, with the darwin Lean toolchain; nothing can be cross-built. Linux-only blockers leave the Signal path. The Linux box keeps the Lean proof work, the gate and Comparator. |

## 3. Architecture

The Lean code and the proofs are two packages, and the code runs as a separate process.
**[amendment]**

```
  Spec   (Crdt, Mathlib)   Finset model: Record, Store, accept, heads, Reach, Fetched, AcceptBuilt
                           obligations: fetched_agree, fetched_build, fetched_union, salvage_maximal,
                           confirmed_exact, authorConfirmed_sound; four limit examples
        │  Bridge.lean (toSpec, hashSpec, abs) + Refine.lean; Api.lean states the results (§3.2)
  Code   (Zrdt, Init+Std)  CheckedStore = RawStore (ExtTreeMap digest→record, head cache, chat id)
                           + Built; constructors: empty, accept; merge / open / salvage via acceptAll
                           observers: heads, has, get, reachSet, encode, classify; sha256, commit
        │  lake build in core/: a standard lean_exe link, no Mathlib, no C of ours
  zrdtd  (process)         Proto.handle over a table of CheckedStore; frames on stdin/stdout (§3.3)
        │  u32 BE length ‖ u8 op ‖ body
  Host   (TypeScript)      Signal-Desktop fork: ZrdtBackend (daemon | stub), hooks, SQL tables, UI;
                           EvilServer (mock server) as villain
```

The host never computes a hash or heads, and never decides whether a record is accepted. It does
choose which messages are records (the scope predicate), pass their bytes, and set provenance
flags. These host duties are in the trusted base (§6). **[amendment]**

If the stored records are corrupted, `OPEN` on reload catches a removed or altered record that
something links, a link to nothing, a changed group and malformed bytes. It does not catch the
removal or edit of the newest record (a head), or an appended forged record: each leaves a valid
history that ends somewhere. That is the same limit as against the server
(`withheld_tail_undetectable`, `tail_replaced_passes_open`). **[amendment]**

If `zrdtd` exits, the host shows "zrdt unavailable" and marks nothing accepted (fail-closed).
**[amendment]**

### 3.1 Repository layout (proposed; `APP.md` may refine the host side) **[amendment]**

```
zrdt/                              this repo (Lean, docs)
  lakefile.toml                    package `zrdt`: lib Crdt (Mathlib), lib Test; requires zrdt-core by path
  core/                            package `zrdt-core`: lib Zrdt, exe zrdtd; Init and Std only, no `require`
    lakefile.toml
    Zrdt/Digest.lean               Digest (32 bytes, lawful bytewise order), Aci, GroupId
    Zrdt/Sha256.lean               SHA-256 in pure Lean; NIST vectors as #guard
    Zrdt/Record.lean               Rec (group, commit, canonical links, author); hashRecord
    Zrdt/Encode.lean               record and blob encode / strict decode; size bounds
    Zrdt/Store.lean                RawStore, Built, CheckedStore, accept, acceptAll, merge, open, salvage
    Zrdt/Commit.lean               protobuf top-level field scan; commit
    Zrdt/Provenance.lean           classify
    Zrdt/Proto.lean                frame codec; handle (§3.3)
    Zrdt/Vectors.lean              #guard vectors; source of vectors/vectors.json
    Zrdtd/Main.lean                zrdtd: the stdin/stdout loop
  Crdt/Merkle/Defs.lean            keep (un-private what other modules need)
  Crdt/Merkle/Integrity.lean       keep (delete _global theorems)
  Crdt/Merkle/Chat.lean            new: spec theorems (proof obligations), limit examples
  Crdt/Merkle/Bridge.lean          new: toSpec, hashSpec, abs; bridge lemmas from Built to the spec
  Crdt/Merkle/Refine.lean          new: refinement theorems
  Crdt/Merkle/Api.lean             new: the advertised statements over CheckedStore (§3.2)
  Crdt/Merkle/EncodeProofs.lean    new: encode_injective
  Crdt/Merkle/LoadSpec.lean        new: salvage in the model (buildRetry inside every store that takes in u) [amendment]
  Crdt/Merkle/LoadApi.lean         new: open and salvage in the model (open_ok_iff_model, salvage_ok_model) [amendment]
  Crdt/Merkle/Classify*.lean       new: Classify, ClassifyFast, ClassifyStatus: CLASSIFY computes `status` [amendment]
  Test/Axioms.lean                 gate: pins exactly the eleven Api names (§3.2)
  Test/Differential.lean           plausible: CheckedStore vs Finset model (not written; see §10)
  vectors/vectors.json
  proxy/                           stretch only: TLS proxy against staging (APP.md §8b)
  docs/PLAN.md docs/PLAN_HUMANS.md docs/APP.md docs/RESTORE_PLAN.md
                                   (plus PHASE1-PROMPT.md, VISIBILITY-AUDIT.md, review-2026-11-01/)
  README.md CLAUDE.md
signal-desktop-zrdt/               separate repo: the fork at v8.33.0, built and run on the Mac mini
  ts/zrdt/ZrdtBackend.std.ts       the async backend interface
  ts/zrdt/backends/daemon.node.ts  spawns $ZRDT_DAEMON; host side of the frame codec
  ts/zrdt/backends/stub.node.ts    day-1 TypeScript stub; the independent reimplementation
  ts/zrdt/*                        scope predicate, send/receive hooks (one call per path), resend,
                                   provenance, import/export
  ts/zrdt/ui/                      zrdt UI: plain props, own CSS, no imports from Signal's ts/
  demo/rules.ts                    pure rule engine, two adapters (EvilServer; the fallback relay)
  demo/evil.ts demo/launch.ts      EvilServer; four Bootstraps, the group, tiling, warm-ups (APP.md §8a)
  demo/doctor.ts                   edits exported stores for beats 4 and 5
  demo/smoke.ts                    Playwright go/no-go test (checkpoint F2)
```

### 3.2 Namespaces and gate names **[amendment]**

Spec theorems live in `Crdt.Merkle`. The code lives in namespace `Zrdt` (`Zrdt.CheckedStore`,
`Zrdt.encode`, …). The advertised statements are in `Crdt/Merkle/Api.lean`, which declares them
in namespace `Zrdt`, as `Zrdt.CheckedStore.*` and `Zrdt.encode_injective` (shown below without
the `Zrdt.` prefix). Then dot notation (`c.agree`) works on the shipped type; inside
`namespace Crdt.Merkle` they would be `Crdt.Merkle.CheckedStore.*`, and `c.agree` would not find
them. The axiom gate and the README pin these full names, and nothing else is advertised as a
result. **[amendment]** (lead to confirm)

**Proved and gated (2026-11-01).** **[amendment]** All eleven are in `Api.lean`, and
`Test/Axioms.lean` pins exactly these names to `[propext, Classical.choice, Quot.sound]`. As
stated in the code:

```lean
theorem CheckedStore.fetched (c) : Fetched hashSpec (abs c) (heads hashSpec (abs c))   -- no collision disjunct
theorem CheckedStore.no_collision (c) : ¬ CollisionIn hashSpec (abs c)
theorem CheckedStore.agree (c d) (h : c.heads = d.heads) :                             -- ExtTreeSet: `=` is by content
    abs c = abs d ∨ CollisionIn hashSpec (abs c ∪ abs d)
theorem CheckedStore.abs_accept (c) (r) : AcceptMeans c r (c.accept r)                  -- AcceptMeans: Refine.lean
theorem CheckedStore.abs_merge (h : c.merge d = .ok e) : abs e = abs c ∪ abs d
theorem CheckedStore.open_iff : CheckedStore.open g b = .ok c ↔
    ∃ u, decodeBlob b = some (g, u) ∧ WellSized u ∧ AcceptBuilt hashSpec (specOf u) ∧
      ¬ CollisionIn hashSpec (specOf u) ∧ (∀ r ∈ u, r.group = g) ∧ abs c = specOf u ∧ c.group = g
theorem CheckedStore.salvage_spec (h : salvage g b = .ok s) (hu : decodeBlob b = some (g, u)) :
    ¬ CollisionIn hashSpec (specOf u) ∧ abs s.store = buildRetry hashSpec (specOf u) ∧
      s.store.group = g ∧
      (∀ d, d ∈ s.dropped ↔ d ∈ digests hashSpec (specOf u \ buildRetry hashSpec (specOf u))) ∧
      StrictlySorted s.dropped
theorem CheckedStore.encode_open (c) : CheckedStore.open c.group c.encode = .ok c      -- exact: extensional maps
theorem CheckedStore.confirmed (c d) (hs : Array Digest)                                 -- "held by the sender"
    (hc : ∀ h ∈ hs, c.has h = true) (hd : ∀ h ∈ hs, d.has h = true) :
    c.reachSet hs = d.reachSet hs ∨ CollisionIn hashSpec (abs c ∪ abs d)
theorem CheckedStore.classify_spec (c) (facts) (d) (st : Zrdt.Status) :                  -- §3.5
    (classify c facts)[d]? = some st ↔
      ∃ r, c.get d = some r ∧ status hashSpec (abs c) (liveOf facts) (toSpec r) = st.toSpec
theorem encode_injective : Function.Injective encode                                   -- EncodeProofs.lean
```

Differences from the earlier text **[amendment]**: `u.map toSpec` is `specOf u`, the *set* of
`u`'s records (a repeated record counts once; order does not matter). `salvage_spec` needs only
that the blob decodes; it concludes there was no collision. `confirmed` takes `c.has h = true` for
each `h ∈ hs`. `classify_spec` uses the spec's `status`, whose `heldBy` names one member, the
smallest holder in byte order of ACIs (§3.5).

Where the proofs are **[amendment]**: `Bridge.lean` (`toSpec`, `hashSpec`, `abs`; `Built` gives
`AcceptBuilt`, the heads and no collision), `Refine.lean` (accept, merge, observers, `reachSet`),
`LoadSpec.lean` (salvage in the model) and `LoadApi.lean` (`open`, `salvage` in the model),
`Classify.lean`, `ClassifyFast.lean`, `ClassifyStatus.lean` (`classify` equals the reference and
computes the spec's `status`), `EncodeProofs.lean` (`encode_injective`).

- `CheckedStore.confirmed` means "held by the sender": the member who sent a live message holds
  what its links reach. That the claimed author wrote a record needs `authorConfirmed` (§3.5),
  which `classify_spec` connects to the code.
- The spec theorems are proof obligations, not results: `fetched_agree` and `fetched_of_build`
  (`Integrity.lean`; the list form), and in `Chat.lean` `fetched_build` (the `AcceptBuilt` form),
  `fetched_union`, `acceptBuilt_union`, `acceptBuilt_insert`, `salvage_built`, `salvage_maximal`,
  `confirmed_exact`, `reach_implies_held`, `authorConfirmed_sound` (with `LiveFacts`,
  `HonestAuthor`, `authorConfirmed`, `foreignMarked`, `holders`, `status`). All are proved.
  **[amendment]**
- The four limit examples (§4 A) are stated next to them and named in the README:
  `withheld_tail_undetectable`, `tail_replaced_passes_open`, `gap_indistinguishable`,
  `relay_attribution_indistinguishable`.
- The **closure gate** (§6, rung 2a) checks the other half of the contract: `zrdtd` links no
  Mathlib.

### 3.3 Frame protocol (`zrdtd`) **[amendment]**

This replaces the old C header. It is the contract the host builds against from day 1 (via the TS
stub) and that phase C freezes.

- **Frames** on stdin/stdout: `u32 BE length ‖ u8 op ‖ body`. `zrdtd` handles one frame at a
  time and replies in request order. Diagnostics go to stderr. The read loop reads until it has
  the full frame (reads can be short). It runs with `LEAN_ABORT_ON_PANIC=1`.
- **One dispatcher**, `Zrdt.Proto.handle : ByteArray → IO ByteArray`, over
  `initialize stores : IO.Ref (Std.HashMap ChatKey CheckedStore)`. A chat key is the host's
  conversation id.
- `handle` takes a store out of the table before it changes it: inside `stores.modifyGet`, erase
  the chat key, run `accept` (or `merge`), then insert the result. The store is then not shared,
  and `accept` updates it in place. Otherwise every accept copies it (review §1.4: 16k inserts
  took 1,350 ms with a copy each time, 2.5 ms without). This matters most for the `Std.HashMap`
  fallback (§7). **[amendment]**
- Byte order is big-endian. Digests, group ids and nonces are 32 bytes; ACIs are 16. Every digest
  list in a reply is sorted. The exact body layout is fixed in `Proto.lean` and pinned by the
  vectors.
- **Protocol 2** **[amendment]** (lane T5, `Proto.protocolVersion = 2`; `Proto.lean`'s header is
  the reference): `ACCEPT` returns the record's bytes with its digest, `COMMIT` returns the
  opening with the commitment, and `ACCEPT_RECORD` (`0x10`) accepts a relayed or imported record
  given as bytes, with its opening if any. The host never builds record bytes or openings itself.
  Status bytes: `OK 0x00`, `MISSING`, `COLLISION`, `WRONG_CHAT`, `TOO_LARGE`, `MALFORMED`,
  `UNVERIFIABLE`, `NOT_FOUND`, `BAD_OPENING 0x08`; request errors from `0x80` (`BAD_REQUEST`,
  `UNKNOWN_OP`, `NO_CHAT`, `CHAT_OPEN`) change nothing.

**There is no unchecked store.** The table holds `CheckedStore` values, so every handle is checked
by its type in the shipped code. A store comes only from `empty` (`NEW`), `accept` (`ACCEPT`,
`ACCEPT_RECORD` **[amendment]**), or the `acceptAll` worklist (`OPEN`, `SALVAGE`, `MERGE`). No op loads a store without checking it,
and there is no raw decode, so the host has nothing to remember to call.

| Op | Request | Reply |
|---|---|---|
| `VERSION` | none | protocol version (2), build id (package version and a hash of the Lean sources `zrdtd` runs) **[amendment]** |
| `NEW` | chat key, group id (32) | `OK` |
| `OPEN` | chat key, group id, blob, or a list of encoded records | `OK` \| `MALFORMED` \| `TOO_LARGE` \| `WRONG_CHAT` \| `COLLISION{digest}` \| `UNVERIFIABLE{unverifiable[], missing[]}` |
| `SALVAGE` | same as `OPEN` | `OK{dropped[], missing[]}` (the store is loaded) \| `MALFORMED` \| `TOO_LARGE` \| `WRONG_CHAT` \| `COLLISION{digest}` |
| `COMMIT` | group id, author (16), nonce (32), DataMessage bytes | commitment (32) ‖ opening (nonce ‖ the bytes without fields 15 and 200) \| `MALFORMED` **[amendment]** |
| `HASH` | record parts | digest (no store needed) |
| `ACCEPT` | chat key, record parts | `ACCEPTED{digest, record bytes}` \| `MISSING{digests[]}` \| `COLLISION{digest}` \| `WRONG_CHAT` \| `TOO_LARGE` **[amendment]** |
| `ACCEPT_RECORD` (`0x10`) | chat key, record bytes, optional opening | as `ACCEPT`, plus `MALFORMED` (not a record's encoding) \| `BAD_OPENING` (the opening's commitment is not the record's commit, or it holds field 15 or 200). Checked before the store is touched. **[amendment]** |
| `HEADS` / `HAS` / `GET` | chat key [, digest] | sorted digests / bool / record parts |
| `REACH_SET` | chat key, from[] | sorted digests |
| `MERGE` | chat key, blob | as `OPEN`, then union into the open store; `COLLISION`/`WRONG_CHAT` leave it unchanged |
| `CLASSIFY` | chat key, live facts (§3.5) | a status per record (§3.5) |
| `ENCODE` | chat key | blob |
| `CLOSE` | chat key | `OK` |

What the replies mean:

- `ACCEPTED{digest, record bytes}`: inserted, or already present (idempotent);
  `digest = hashRecord r`, and the bytes are the record's canonical encoding (links sorted,
  repeats dropped), the bytes to relay or store. **[amendment]** A
  byte-identical duplicate is accepted, not a collision.
- `MISSING{digests}`: store unchanged; exactly the links that do not resolve (non-empty).
- `COLLISION{digest}`: store unchanged; a different record with this digest is already stored.
- `WRONG_CHAT`: store unchanged; the record's group is not this store's group.
- `TOO_LARGE`: store unchanged; beyond the limits of §3.4. A blob whose count field is 2^24 or
  more is `TOO_LARGE` before any record is read. **[amendment]**
- `BAD_OPENING` (`ACCEPT_RECORD` only): nothing changed; the opening does not belong to the
  record. The fork then retries without the opening (structure only). **[amendment]**
- `OPEN` → `OK`: every record was accepted. `UNVERIFIABLE`: no store is loaded; `unverifiable`
  lists every record that could never be accepted (a link to nothing, or a cycle), and `missing`
  the link digests that point to nothing. This is the "rejected restore" of demo beat 4.
- `SALVAGE` → `OK`: the accepted part is loaded (the largest subset any client could have
  accepted, `salvage_maximal`); `dropped` names the rest.

Why the certificate is "accept-built" rather than "fetched from own heads": the latter is not
closed under union in the model (two records linking each other form a cycle that is reachable
from a head but can never be accepted). "There is an order in which every record's links resolved
before it was inserted" is closed under `accept`, `merge` and `salvage`, excludes cycles by
construction, and implies fetched-from-own-heads or a collision (`fetched_build`).

**Host side (in the fork):**

- `ts/zrdt/ZrdtBackend.std.ts`: one async interface.
- `ts/zrdt/backends/daemon.node.ts`: spawns `$ZRDT_DAEMON` from the main-window preload, or from
  the main process via `ipcMain.handle`.
- `ts/zrdt/backends/stub.node.ts`: the day-1 TypeScript stub. Later it is the independent
  reimplementation for the differential test (rung 7).
- When the daemon exits, the host shows a "zrdt unavailable" banner and marks nothing accepted.
  On restart it re-`OPEN`s each chat from its SQL rows.
- `ZRDT_REQUIRE_LEAN=1` refuses the stub. The backend's kind and version are shown on screen.

**Optional stretch, macOS only:** an in-process `.node` with `@[export zrdt_l_call]` over the same
`handle`. It needs about 20 lines of C, copies every output (Electron rejects external buffers),
and guards every entry with an initialised flag. The shipped Linux `libleanrt.a` cannot be linked
into a `.node` (local-exec TLS); macOS is very likely fine.

### 3.4 Encodings (shared by Lean `encode`, the TS stub and the vectors) **[amendment]**

- **Record** (`Encode.lean`, hashed by `hashRecord r := sha256 (encode r)`):
  `"zrdt2" ‖ group(32) ‖ commit(32) ‖ u32 nlinks ‖ links (strictly sorted, no duplicates, 32 each) ‖ author(16)`.
  - Every field has a fixed size except one array of fixed-size elements, so
    `encode_injective : Function.Injective encode` holds with no size bound.
  - The chat id is inside the hash, so a record from another chat, resent or imported, is
    rejected on arrival (`WRONG_CHAT`).
  - The author is the sender's ACI. Links are a canonical type: a strictly sorted array of
    distinct digests, built by the single record constructor. Link order cannot change the hash,
    and decoding rejects non-canonical records.
- **Commitment**: `commit = SHA-256("zrdtP1" ‖ group ‖ author ‖ nonce(32) ‖ DataMessage wire bytes
  with top-level fields 15 (groupV2, which contains the group master key) and 200 (zrdt) removed)`.
  - Lean computes it (`COMMIT`). The host never hashes.
  - The timestamp and everything the user sees (body, quote, mentions, attachments, previews,
    stickers) are inside it.
  - The nonce is 32 random bytes per message, carried in `ZrdtMeta.nonce`.
- **Store blob** (`encode` on a store): `"zrdtS2" ‖ group(32) ‖ u32 count ‖ (u32 len ‖ record)*`,
  sorted by digest. Heads are not stored; `open` recomputes them. `encode_open` is exact, because
  the maps are extensional. The decoder takes the records in any order, and a byte-identical
  repeat counts once (`specOf`, §3.2). **[amendment]**
  - Limits: count < 2^24 and nlinks ≤ 4096. `Built` includes them; `accept` and `open` return
    `TOO_LARGE` beyond them. A count field of 2^24 or more is `TOO_LARGE` before any record is
    read (`blobTooLarge`). **[amendment]**
  - The decoder never sizes an allocation from an untrusted count. A fuzz vector checks this.
- **The store holds structure only.** The content (the opening: the nonce plus exactly the
  committed bytes, i.e. the DataMessage with fields 15 and 200 already removed) lives in Desktop as
  a new message attribute, `zrdtOpening`, marked `erase` in `messageAttributesEraseBehavior`.
  Desktop's delete, expiry and view-once paths remove it. No opening (stored, relayed or dumped)
  carries the group master key; the host supplies the group context from the conversation when it
  re-enters an opening. The frozen send copy `message.zrdt` is classified `erase` too.
  **[amendment]**
- **Digest in protobuf**: raw 32 bytes. **Compare code in the UI** (see `APP.md`): "Copy compare
  code" carries the full sorted heads set. Words are only an "equal?" fingerprint, of at least 12
  words (128 bits).

### 3.5 Record mapping (Signal)

**Which messages are records** (the scope predicate, one function shared by send and receive): a
GroupV2 `DataMessage` from the `NormalMessage` job with no `storyContext`, no `reaction` and no
`editedMessageTimestamp`. A `zrdt` field on anything else is ignored. **[amendment]**

**Fields**: group = the group's 32-byte identifier; commit = the commitment of §3.4 (the
timestamp is inside it); links = the sender's heads at send time; author = the sender's ACI.
**[amendment]**

**Wire format** **[amendment]**:

```proto
message ZrdtMeta {
  repeated bytes links   = 1;   // 32-byte digests: the sender's heads at send time
  optional bytes nonce   = 2;   // 32 bytes, the commitment salt
  optional uint32 version = 3;
  repeated bytes disown  = 4;   // digests of records in the sender's name it did not create
}
message DataMessage { ... optional ZrdtMeta zrdt = 200; }   // present ⇒ record, if in scope

message ZrdtResendRequest { bytes groupId = 1; repeated bytes digests = 2; }
message ZrdtResend        { bytes groupId = 1; bytes record = 2; optional bytes opening = 3; } // opening = nonce ‖ DataMessage bytes without fields 15 and 200
message ZrdtNotFound      { bytes groupId = 1; repeated bytes digests = 2; }
message Content { oneof content { ...; ZrdtResendRequest zrdtResendRequest = 200;
                                       ZrdtResend zrdtResend = 201; ZrdtNotFound zrdtNotFound = 202; } }
```

- The control messages sit inside `Content`'s `oneof`. That matches `MessageReceiver`'s dispatch
  and adds no required key to the many `Content` literals.
- Stock clients log "Unsupported content message" at error level and drop the unknown `Content`.
  Nothing is rendered.

**Recovery by digest** **[amendment]**:

- The request goes 1:1 to the member whose message referenced the digest first, then to the
  group. Replies are always 1:1.
- **Relay:** the responder sends `ZrdtResend{record, opening}` (the record bytes from its
  `ACCEPT`/`GET`, the opening from its `COMMIT`). The receiver calls
  `ACCEPT_RECORD(chat, record, opening)`: `zrdtd` checks that the bytes are a record and that the
  opening's commitment is the record's commit, then accepts it; the returned digest must be one
  that was asked for. On `BAD_OPENING` the receiver accepts the record without the opening
  (structure only, "content unavailable"). It shows the message as "relayed by X"; it becomes
  normal once author-confirmed. **[amendment]** (protocol 2; replaces the host-side `HASH` and
  `COMMIT` comparison)
- **Author fast path:** once the record arrives, the receiver knows its author and asks the
  author 1:1. The author re-sends the original through Desktop's sendLog/`SavedProto` path
  (`handleRetry.preload.ts:236-245`). That copy arrives `live`, so it is author-confirmed at once.
  The sendLog serves only within 24 h; it is pruned per recipient on delivery receipts, but a
  victim who never acknowledged keeps its entry.
- **Relayed messages never apply side-effect fields.** `handleDataMessage.preload.ts:687-711`
  sets the sender's `profileKey` for group messages; a relay must not. The same goes for the
  expire timer, group changes and anything outside the scope predicate.
- If the author's live copy arrives later, it upgrades the provenance of the same digest. The
  `(sent_at, sourceServiceId)` dedupe never silently drops a copy whose digest differs.
- **`ZrdtNotFound` is not decisive.** The server can drop the request or the reply, and an honest
  member may lack the record (another of their devices linked it, or the store was salvaged,
  relinked or erased). A not-found from a member for a digest they linked is evidence of
  inconsistency, not of malice.

**Provenance and attribution** **[amendment]**:

- Per record, host state, trusted: `live` (the Signal envelope sender equals the record's author,
  or this device sent it), `relayed(byAci)`, or `imported`.
- `authorConfirmed r` ⇔ some `live` record from `r.author` reaches r, and no `live` record from
  `r.author` lists r in `disown`. `authorConfirmed_sound`: if every live record of an author lists
  in `disown` each record in its name that it reaches and that the author did not create, then
  every author-confirmed record attributed to it was created by it, or two records collide.
  **[amendment]** (lead to confirm)
- `CLASSIFY` takes the live facts (the provenance per record and the `disown` lists of live
  records) and returns per record: `confirmedByAuthor` (`authorConfirmed` holds); `heldBy(aci)`
  (reached by a live record of another member; one ACI, the smallest in byte order, so every
  device names the same member **[amendment]**, lane T5); `unconfirmed` (no live record reaches it); or
  `notConfirmedByAuthor` (the author has a live record concurrent with it and no live record from
  the author reaches it, or a live record from the author lists it in `disown`). When several
  statuses apply, the order is `confirmedByAuthor`, `notConfirmedByAuthor`, `heldBy`,
  `unconfirmed`: a fake in A's name that member M links live and that A disowns shows "not
  confirmed by A", not "held by M". It is decided by reachability and `disown`, never by receive
  order, so the server cannot cause false accusations by reordering. **[amendment]** (lead to
  confirm the order)
- **Never refuse a record in your own name.** Refusing would stall everything that links it.
  Accept it, alarm locally ("someone linked a message in your name you did not send"), and list
  it in `ZrdtMeta.disown` in **every** later message: `disown` carries every record in your name
  that your heads reach and that you did not create. Only `disown` lists that arrive live count,
  so a one-time disown would be lost for any member who missed that one message live (the server
  dropped it, it came relayed, or the member imported later). **[amendment]**
- "Confirmed by" (formerly "seen by"), the fork marker and "A's latest" use `live` records only.
  In the optional "confirmed by" list, "confirmed by X" means that a live message of X reaches
  the record, so X holds it. It says nothing about who wrote it; only the author label
  (`confirmedByAuthor`) does. **[amendment]**

Whole-history restore from any source: `RESTORE_PLAN.md`, with the privacy rules of phase D.

## 4. Work breakdown

Effort is in agent-days of one continuously working agent. Lanes run in parallel in separate git
worktrees (§5). The lead merges serially. The Lean lanes (L1–L3) run on the Linux box; `zrdtd` is
also built on the Mac. The Signal lanes (H1–H3) run on the Mac mini. **[amendment]**

### Phase A — Lean spec cleanup + `Chat.lean` (lane L1, 1 day, no dependencies)

Deliverables:
- Delete `Crdt/Merkle/TaskList.lean`, its import in `Crdt.lean`, its three gate lines in
  `Test/Axioms.lean` (`add_wins`, `fetched_live_agree`, `remove_requires_closure`).
- Delete from `Integrity.lean` the seven `*_global` theorems and `merge_fetched`; from `Defs.lean`
  `Collision`, `CollisionIn.global`, `Receipt`, `receipt`, `receipt_heads_sound`,
  `receipt_confirms`, `heads_insert_of_links_heads`. Remove `private` from `digests_union`,
  `digests_empty`, `mem_heads`, `closed_build` (`Defs.lean:259`) and the `Toy` namespace. Fix the
  line-length drift (≤ 100 chars). **[amendment]**
- `Crdt/Merkle/Chat.lean`, namespace `Crdt.Merkle`, each with docstring + concrete example. These
  are proof obligations for `Api.lean` (§3.2), not advertised results. **[amendment]**
  - `fetched_union : Fetched hash s hs → Fetched hash t ht → Fetched hash (s ∪ t) (hs ∪ ht)`
    (no collision clause needed) and the lemma `heads_union_subset`.
  - `reachSet`, `mem_reachSet`, `reach_reachSet`, `fetched_reachSet`, and
    `confirmed_exact : Closed hash s → Closed hash t → hs ⊆ digests hash s → hs ⊆ digests hash t →
    reachSet hash s hs = reachSet hash t hs ∨ CollisionIn hash (reachSet hash s hs ∪ reachSet hash t hs)`.
    Proofs are in `RESTORE_PLAN.md`'s appendix; paste and adapt.
  - `AcceptBuilt hash s := ∃ l, l.toFinset = s ∧ build hash l = s`; `buildRetry hash u` (accept
    every record of `u` whose links resolve, repeat until no change; fuel = `u.card`, which is
    exactly tight); `salvage_built : AcceptBuilt hash (buildRetry hash u)` and
    `salvage_maximal : AcceptBuilt hash s → s ⊆ u → s ⊆ buildRetry hash u`. Corollaries:
    `acceptBuilt_union`, `acceptBuilt_insert` (closure under `accept`), and `fetched_build`
    restated as `AcceptBuilt hash s → Fetched hash s (heads hash s) ∨ CollisionIn hash s`.
    `fetched_union`, `acceptBuilt_union` and `salvage_maximal` are true as stated, even with
    collisions (checked in the review). **[amendment]**
  - `authorConfirmed` over a store plus the host's provenance facts; the spec status of a record
    (the four values of §3.5 and their order) as a function of the store and the live facts,
    which `classify_spec` (§3.2) refers to; and `authorConfirmed_sound` (§3.5): if every live
    record of an author lists in `disown` each record in its name that it reaches and that the
    author did not create, then every author-confirmed record attributed to it was created by it,
    or two records collide. **[amendment]** (lead to confirm)
  - Limit examples (`example`, `decide`-able, over a local toy hash) **[amendment]**:
    1. `withheld_tail_undetectable`: a withheld newest record passes every local check;
    2. `tail_replaced_passes_open`: a store whose tail was replaced by a consistent fake passes;
    3. `gap_indistinguishable`: two worlds that differ only in whether another member holds a
       record give the phone the same view;
    4. `relay_attribution_indistinguishable`: without disown, "Alice wrote F and the server
       dropped it" and "Mallory forged F" give a third member identical views.
- Lemmas kept but not advertised: `closed_accept`, `closed_union`, `complete_of_closed`,
  `heads_insert`, `accept_unique`, `eq_of_digests_eq`, `heads_subset_digests`, `Reach.lift`,
  `Reach.mem_of_bound`, `reach_implies_held`. Do not add one-line restatements as named theorems
  (`no_silent_exclusion`, `fork_visible`, `sender_holds_links`, `resend_verifies` and the like were
  considered and dropped: each is an existing lemma applied once).
- Gate lines for `fetched_union`, `confirmed_exact`, `salvage_maximal`, `authorConfirmed_sound`.
  At the end of phase B the gate pins exactly the `Api.lean` list (§3.2) instead. **[amendment]**

Done when: `lake build` succeeds with no `sorry` warnings; `lake exe axiom_check` prints
`axiom gate passed`; every gated theorem shows `[propext, Classical.choice, Quot.sound]` or fewer;
`grep -rn "sorry\|admit\|native_decide" Crdt/Merkle` is empty; every advertised theorem has a
concrete instance with hypotheses discharged.

### Phase B — package split, `CheckedStore`, refinement, `Api.lean` (lane L2, 3–4 days; the core verification deliverable) **[amendment]**

Order inside the lane: create `core/` and `require` it from the root → `Digest` → `Sha256` →
`Record` → `Encode` → `Store` (compiling, `#eval`-able) → publish the `Store.lean` signatures to
lane L3 → `Provenance` → `Bridge` → `Refine` → `EncodeProofs` → `Api` (last).

Deliverables in `core/` (namespace `Zrdt`; imports `Init` and `Std` only):
- **Package**: `core/lakefile.toml` for `zrdt-core`, with `lean_lib Zrdt` and `lean_exe zrdtd`
  (root `Zrdtd.Main`) and no `require`. The root `lakefile.toml` `require`s `zrdt-core` by path.
- `Digest.lean`: `Digest`, a 32-byte ByteArray with a size proof, `deriving DecidableEq`. Its order
  compares `bytes.data.toList` lexicographically, with `Std.TransOrd` and `Std.LawfulEqOrd`.
  `Aci` (16 bytes) and `GroupId` (32 bytes).
- `Sha256.lean`: SHA-256 in pure Lean, about 70 lines, NIST vectors as `#guard`. No `@[extern]`,
  no `opaque`, no C. A prototype from the review exists, kept outside the repo (`~/devel/zrdt-review-spikes` on the reviewer's machine).
- `Record.lean`: `Rec` (`group`, `commit`, `links`, `author`), with canonical links built only by
  the single record constructor. `hashRecord r := sha256 (encode r)` is computable: it runs under
  `#eval`, and under `decide +kernel` on small examples.
- `Encode.lean`: record `encode` and strict `decode` (rejects non-canonical records), blob encode
  and `decodeBlob`, `WellSized` (§3.4 limits). Never size an allocation from an untrusted count.
- `Store.lean`:
  - `RawStore` is public: `group`, `map : Std.ExtTreeMap Digest Rec compare`, and the head cache
    `heads : Std.ExtTreeSet Digest compare`. The encapsulation is the daemon boundary.
  - `structure Built (c : RawStore) : Prop`: every key is its record's hash; every record has the
    store's group; the head cache equals the keys no record links; there is an accept-order
    witness (newest first) whose members are exactly the map's values; the size bounds of §3.4
    hold. Closure (every link is a key) follows.
  - `CheckedStore := { raw : RawStore, built : Built raw }`. The proof field is erased.
  - Constructors: `empty (g : GroupId)`, and
    `accept : CheckedStore → Rec → AcceptResult × CheckedStore` with `rawAccept_built`, where
    `AcceptResult | accepted (d) | missing (ds) | collision (d) | wrongChat | tooLarge`. A
    prototype from the review exists, kept outside the repo (`~/devel/zrdt-review-spikes` on the reviewer's machine).
  - One worklist, `acceptAll : CheckedStore → Array Rec → CheckedStore × Array Rec`, which
    inserts only through the checked `accept`: count unresolved links per record, accept the
    records whose count is zero, decrement their dependants (Kahn's algorithm, with
    `termination_by`). `merge`, `open` and `salvage` are defined from it, so `Built` holds by
    construction. A bug in the worklist can only reject records or leave leftovers. `open`
    demands an empty leftover list.
  - Observers: `heads`, `has`, `get`, `reachSet` (worklist, `termination_by`), `encode`.
  - Fallback if the extensional maps stall: `Std.HashMap` with `Equiv`-form statements.
- `Provenance.lean`: `classify` (§3.5).
- Everything computable: `#eval` each operation on the `Toy` scenario.

Deliverables in `Crdt` (Mathlib):
- `Bridge.lean`: `LinearOrder Digest` lifted from the bytewise order;
  `toSpec : Rec → Record Payload Digest Aci` with `Payload = (group, commit)` and links as a
  `Finset`; `hashSpec` with `hashSpec (toSpec r) = hashRecord r`; `abs c : Store`; and the bridge
  from `Built` to `AcceptBuilt hashSpec (abs c)`, to the head cache being right, and to there
  being no collision.
- `Refine.lean`: one refinement theorem per constructor and observer, through `abs`: `accept`,
  `acceptAll`, `merge`, `open`, `salvage`, `encode`, `heads` (`heads_eq`), `has` (`has_iff`),
  `get`, `reachSet` (`reachSet_iff`) and `classify`. The `missing` list is exact (sound and
  complete). These are the proofs of the `Api.lean` statements.
- `EncodeProofs.lean`: `encode_injective : Function.Injective encode`, with no size bound.
- `Api.lean`: the statements of §3.2.
- `Test/Differential.lean`: `plausible` properties comparing `CheckedStore` to the finset model
  through `abs` on random record lists (the generator draws links from digests of earlier records
  so links sometimes resolve): `acceptAll` matches the model's `build`, heads agree,
  `open ∘ encode` round-trips, `salvage` agrees with `buildRetry`. Run these *before* proving.
- Gate lines: exactly the §3.2 list.

Done when: all of the above build with no `sorry`; the gate passes; `lake build` has no new
warnings; `cd core && lake build` succeeds on a machine with no Mathlib (rung 2a);
`grep -rn "import Mathlib\|import Crdt" core/` is empty; `#eval` of each operation on the `Toy`
scenario matches the model; the differential tests pass.

### Phase C — `zrdtd`, frame protocol, vectors, TS-stub differential (lane L3, 1–1.5 days; needs B's `Store.lean` signatures) **[amendment]**

**Day-1 spike** (part of checkpoint F0; unblocks every lane): `Proto.lean` with `VERSION`, `NEW`,
`ACCEPT` and `HEADS` over whatever `Store` exists (the spike's `Store.lean` is fine), `zrdtd`
built on Linux and on the Mac, and in the fork the backend interface, both backends, and the
backend's kind and version on screen. Pass: one `ACCEPT` round trip inside the fork's Electron;
`kill -9` on `zrdtd` brings up the banner; the stub is refused when `ZRDT_REQUIRE_LEAN=1`.
Optional, time-boxed to 2 h on the Mac: the in-process `.node` stretch (§3.3).

Deliverables:
- `Commit.lean`: the protobuf top-level field scan that removes fields 15 and 200, and `commit`
  (§3.4). Unproved and small; it is in the trusted base.
- `Proto.lean`: the frame codec and `handle` with every op of §3.3; sorted digest lists.
- `Zrdtd/Main.lean`: the stdin/stdout loop; reads until each frame is complete; diagnostics to
  stderr.
- `Vectors.lean`: `#guard` vectors, and a `main` that prints `vectors/vectors.json`: NIST SHA-256,
  record and blob encodings, `COMMIT`, every reply of every op, and a fuzz vector with an oversize
  count. `make vectors` regenerates the file:
  `cd core && lake build && lake env lean --run Zrdt/Vectors.lean > ../vectors/vectors.json`.
  `Vectors.lean` stays out of `zrdtd`'s imports, so the two `main`s never meet. **[amendment]**
  (lead to confirm)
- The closure check (rung 2a) on the linked `zrdtd` binary.
- `zrdtd` built on the Mac with the darwin Lean toolchain (nothing is cross-built), and on Linux.
  The fork points to it by path (`$ZRDT_DAEMON`); no binaries are vendored into the fork.
- In the fork: `ZrdtBackend.std.ts` and `backends/daemon.node.ts` (§3.3), and the differential
  test that runs `vectors.json` through the TS stub and through `zrdtd` and diffs the replies.

Done when: `zrdtd` builds in `core/` on Linux and on the Mac with no Mathlib; the closure check
prints nothing; rung 6 passes on both machines; rung 7 passes on the Mac; `kill -9` on `zrdtd`
shows the banner and nothing is marked accepted.

### Phase D — Signal-Desktop fork (lanes H1 transport, H2 UI; 5–6 days; starts day 1 against the TS stub; on the Mac mini) **[amendment]**

See `APP.md` for the detail. Pinned at `v8.33.0` (`be0ed1340b9798323d59129b43504062d235e23d`),
Electron 44.9.1, Node 24.22.0, pnpm 11.24.0 (`npm i -g pnpm@11.24.0`). Deliverables in brief:
- **Proto**: `ZrdtMeta` and the `Content` messages of §3.5.
- **Scope predicate**: one function, used on send and on receive (§3.5).
- **Send hook**: inside `conversation.queueJob` in `ts/jobs/helpers/sendNormalMessage.preload.ts`,
  after attachments are uploaded. Freeze once:
  1. links = `HEADS`;
  2. generate a nonce;
  3. build the Content bytes with `ZrdtMeta`;
  4. `COMMIT`, then `ACCEPT`;
  5. persist `message.zrdt = {links, nonce, digest, contentBytes}` first and the store row second;
  6. send the frozen bytes on every attempt;
  7. at startup, re-accept outgoing messages whose digest is missing.

  Extend `getAttrsFromGroupOptions`. `send.preload.ts` is not the hook: it only awaits a send that
  has already started.
- **Receive hook**: in `ts/textsecure/MessageReceiver.preload.ts`. Take the plaintext DataMessage
  bytes (for sync transcripts, `SyncMessage.sent.message`); add dispatch for `Content` 200–202;
  accept after the membership check and before the local-policy drops; mark `live` when the
  envelope's sender ACI equals the record's author; re-enter Desktop only at `handleDataMessage`,
  through the scope predicate.
- **Gaps and recovery**: on `MISSING`, insert a `zrdt-gap` message (it takes the referencing
  message's `received_at`, with `sent_at − 1`; the referencing message is restamped), wait
  `ZRDT_RESEND_DELAY_MS`, then request per §3.5. Recovered records are saved with the gap's
  `received_at`, and the gap row is deleted once it resolves. Do not reuse `retryPlaceholders`.
  Answer requests from `GET` plus the stored opening, or with `ZrdtNotFound`.
- **Persistence**: a SQL migration with `zrdt_records(conversationId, digest, record)`
  (append-only, structure only), `zrdt_pending(conversationId, digest, record, messageId)` and
  `zrdt_provenance(conversationId, digest, kind, byAci, disownedBy)`. Not `items`: its values are
  JSON-stringified, so bytes are corrupted on reload. The opening is the `zrdtOpening` attribute
  (§3.4); Desktop keeps no DataMessage bytes of its own. On load, `OPEN` from the rows; on failure
  the rejected banner names the `missing` digests, with `SALVAGE` behind "Keep what verifies".
  Salvaged records start `imported`.
- **Provenance and disown**: the three values of §3.5, `CLASSIFY` for the display, and the
  own-name alarm with `ZrdtMeta.disown`, which every later message carries in full (§3.5).
  **[amendment]**
- **Restore from anyone** (`RESTORE_PLAN.md`): export and import from Settings → Internal.
  - A dump is the store blob plus a content section keyed by digest (the openings). Openings never
    contain field 15 (`groupV2`, the group master key; §3.4), so a dump carries no master key, and
    the importer's check `COMMIT(opening) == record.commit` holds as is (`RESTORE_PLAN.md` §3,
    update §4.5). **[amendment]**
  - The exporter leaves out content for `expireTimer > 0`, deleted-for-everyone and view-once
    messages; the importer refuses such entries. A member who joined after a record was sent gets
    a structure-only dump.
  - Export needs OS authentication and a "do not share" warning. No "mirror" or "server"
    transport unless the dump is encrypted.
  - Import: on a device with no store, `OPEN` the dump's blob; on a device with a store, `MERGE`
    it (`MERGE` runs the `OPEN` checks, then unions; on failure the open store is unchanged).
    Imported records start `imported`; unconfirmed ones are shown in a collapsed section without
    avatars or live links, never inline under a member's name. **[amendment]**
  - Say plainly: stock link-and-sync and Signal backups carry no zrdt data, so a device restored
    that way has a full timeline and an empty store.
- **UI states**: gap row; compare ("Copy compare code" / "Paste compare code", with the outcomes
  identical / they're behind / you're behind / "Bob has N messages you don't … Asked; no answer."
  and "Ask again"); rejected banner; "relayed by X", "held by X", "confirmed by A",
  "not confirmed by A"; the own-name alarm; "zrdt unavailable"; backend kind and version.
  Wording names what differs, never who is at fault. Optional, not in the demo criteria:
  "confirmed by" checkpoints (X holds the message, which says nothing about authorship, §3.5), the
  fork marker (on `(author, sent_at)` with different digests) and "A's latest", all from `live`
  records only. **[amendment]**
- **Blocking** is a permanent divergence in both directions. Document it.

Done when: four instances against the evil server with all rules off behave like stock Signal;
every UI state is reachable with the TS stub; then the backend is switched to `zrdtd` with no hook
code change (the frame protocol is the contract).

### Phase E — Villain and launch harness (lane H3, 1.5–2 days; starts day 1; on the Mac mini) **[amendment]**

`EvilServer extends Server` from `@signalapp/mock-server`, in the fork at `demo/evil.ts`. It
overrides `handleMessage` (for `deviceId ≠ 1`) and `prepareMultiDeviceMessage`, **not `send()`**.
Detail in `APP.md` §8a. A sketch, checked against the mock-server API but untested and with two
known defects (review §3.1), exists from the review, kept outside the repo (`~/devel/zrdt-review-spikes` on the reviewer's machine).

- **Rules** (pure functions in `demo/rules.ts`, so the fallback can reuse them):
  - `dropGroupMsg(from, to)`, once, matching recipients ≥ 2 and the inferred sender;
  - `blackhole(to)`, which discards;
  - `hold(to)` / `release(to)`.

  Arm rules only after the warm-up sends. No `replay` (Signal already discards replays) and no
  `reorder`. Controls: a tiny panel (HTTP `/rules`, `/log`) or REPL.
- **The server can infer the sender** of a group message from the recipient set (the group minus
  the sender) and from the sender's own authenticated `SyncMessage.Sent` with the same timestamp.
  So "drop Alice's message to Carol" is real server power. The mock holds every key, so the rules
  are limited by policy to what a real server sees.
- **Harness** (`demo/launch.ts`, about 300–400 lines):
  - `ciMode: 'full'` is required (`link()` needs `window.SignalCI`). Its retry unit is 10×
    shorter, so set explicit demo timeouts.
  - Four Bootstraps (Alice, Bob, Carol, Dave) with `contactCount: 0`, a `phoneName` patch, and
    the group plus the other members in **every** phone's storage state.
  - Link Alice's, Bob's and Carol's desktops one after another, then tile the windows; each sends
    one warm-up message. Dave's desktop is linked just before beat 5 and sends nothing before its
    import. **[amendment]**
  - To restart, use `app.close(); app.start()`, **never** `bootstrap.startApp()`, which wipes the
    profile on a failed start.
- `demo/doctor.ts`: removes a linked, non-head record from an export (beat 4); appends two fakes
  attributed to Bob on top of the genuine head of Bob's export, automatically (beat 5).
- `demo/smoke.ts` (Playwright): the F2 go/no-go test.
- **Day-1 spike**: desktops exchange sender-key group messages through the mock.

Done when: each rule demonstrably changes what a fork receives; with all rules off, the four
desktops behave normally; the launch script runs from cold in one command.

Stretch, only after beats 1–5 pass: a TLS-terminating proxy in front of `chat.staging.signal.org`
with the same rule set, for a demo against the real network (`proxy/`; APP.md §8b, including the
open question whether libsignal-net honours a custom `certificateAuthority`).
`SIGNAL_ENABLE_HTTP` is not a TLS escape hatch. Also stretch: "a stock client keeps working",
which needs a separate upstream worktree, since the mock setup has no stock client.

### Phase F — Demo assembly, README, Comparator, docs (1–2 days; depends on all)

- Rehearse the five beats (§8) twice from cold start; write `DEMO.md` with the exact clicks.
  **[amendment]**
- README: what is proved (the `Api.lean` statements in plain English); the trusted base (the Lean
  compiler and runtime; the frame codec and protobuf field scan, which are Lean but unproved and
  small; the TS client; the host duties: provenance flags, passing the right bytes, the scope
  predicate, UI wording; there is no C and no external SHA-256); what is not proved (§1 non-goals
  and the four limit examples); that links are receipts visible to the whole group; the sourced
  comparison with Signal, MLS and Keybase (from `PLAN_HUMANS.md`). **[amendment]**
- Comparator: `Comparator/Challenge.lean` with the `Api.lean` statements and `sorry` bodies;
  `comparator.json` per `lake help comparator` (permitted axioms: `propext`, `Classical.choice`,
  `Quot.sound`); `make comparator` runs `lake comparator` inside a Linux Docker image with `bwrap`;
  also `lake check`. Both must pass. **[amendment]**
- Keep `PLAN.md`, `PLAN_HUMANS.md`, `APP.md` and `RESTORE_PLAN.md` current; the lead updates §10
  at each merge.

### Critical path and parallelism **[amendment]**

```
day 1:  A.cleanup ───────────┐
        E.harness spike      │ (parallel from day 1; D and E on the Mac)
        D.transport, D.ui    │ against the TS stub
        C.zrdtd spike ───────┤ F0: one ACCEPT round trip inside the fork's Electron
        B.split + Digest/Sha256/Record/Encode/Store ──► C.Proto+vectors+differential
                   │                                        ──► D.switch stub→zrdtd (F4) ──► F.demo
                   └──► B.Provenance/Bridge/Refine/Api (longest Lean task; runs beside C and D)
```

Critical path ≈ D (5–6 d from day 1, against the stub) → D.switch at F4 (day 6) → F (1–2 d). The
Lean code path, B up to `Store.lean` then C (1–1.5 d), must land before F4; B's proofs run
alongside. If B.Refine slips, the demo still ships on the unproved code, and the README says
exactly which refinement theorems are missing. Never ship a `sorry` to make it look proved.

### Agent roster and file ownership (disjoint; no two agents edit one file)

| Agent | Owns | Lane |
|---|---|---|
| lean-spec | `Defs.lean`, `Integrity.lean`, `Chat.lean`, gate lines for A | L1 |
| lean-impl | both `lakefile.toml`s; `core/Zrdt/Digest.lean`, `Sha256.lean`, `Record.lean`, `Encode.lean`, `Store.lean`, `Provenance.lean` **[amendment]** | L2 |
| lean-refine | `Bridge.lean`, `Refine.lean`, `EncodeProofs.lean`, `Api.lean`, `Test/Differential.lean`, gate lines for B **[amendment]** | L2 (after `Store.lean` compiles) |
| zrdtd | `core/Zrdt/Commit.lean`, `Proto.lean`, `Vectors.lean`, `core/Zrdtd/Main.lean`, `vectors/*`, Makefile targets for `zrdtd`, vectors and the closure check; fork `ts/zrdt/ZrdtBackend.std.ts`, `ts/zrdt/backends/daemon.node.ts`, the vector differential test **[amendment]** | L3 |
| desktop-transport | fork: the shared root files (`protos/SignalService.proto`, `ts/textsecure/MessageReceiver.preload.ts`, `ts/jobs/helpers/sendNormalMessage.preload.ts` with `getAttrsFromGroupOptions`, the SQL migration with `ts/sql/Server.node.ts` and `Interface.std.ts`, `ts/model-types.std.ts` and `messageAttributesEraseBehavior`, lint suffix rules); `ts/zrdt/*` outside `ui/`, `ZrdtBackend.std.ts` and `daemon.node.ts`, including the stub **[amendment]** | H1 |
| desktop-ui | fork: `ts/zrdt/ui/*`, and the Signal timeline files the `zrdt-gap` type touches (`getPropsForMessage`, `isMessageEmpty`, the `TimelineItem` switch) **[amendment]** | H2 |
| villain | fork `demo/*` (evil, rules, launch, doctor, smoke) and the bootstrap `phoneName` patch; `proxy/*` only for the stretch **[amendment]** | H3 |
| docs-demo | `README.md`, `DEMO.md`, `Comparator/*`, `make comparator` | F |

Other agents ask the owner of a shared root file for any change to it. Keep the zrdt code in
`ts/zrdt/` with one hook call per path, so the diff to Signal stays small. **[amendment]**

The lead: merges serially, approves statement changes, keeps §10 current, reruns the gate after
every merge.

## 5. Rules for agents

From `CLAUDE.md`, restated as hard rules:

1. **One `lake` process per checkout** (`core/` is part of the checkout). Never two `lake`
   invocations, or `lake` plus a REPL, in one worktree at once. Parallel Lean agents each work in
   their own git worktree (`git worktree add ../zrdt-<agent> -b <agent>/<topic>`), run
   `lake exe cache get` there, and never symlink another worktree's `.lake`. On the Linux box,
   extend the LV before creating Lean worktrees (§7). **[amendment]**
2. **Build one module per edit**: `lake build Crdt.Merkle.<Module>` or `lake build Zrdt.<Module>`.
   Full `lake build` at checkpoints. Read the warnings: a successful build can still contain
   `sorry`. **[amendment]**
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
9. **Never edit generated files** (protobuf outputs, `vectors.json`): regenerate them
   (`make vectors` for `vectors.json`, phase C). **[amendment]**
10. **Git**: stage only files you touched; the lead merges serially; commit messages end with
    `Co-Authored-By: Claude Fable 5.1 <noreply@anthropic.com>`. Do not commit `.lake`.
11. **Report faithfully**: failed builds, skipped steps, and anything unusual go in the hand-back,
    in the first line.
12. **Nothing under `core/` imports Mathlib or `Crdt`.** Theorems about `Zrdt` definitions go in
    `Crdt`. **[amendment]**

## 6. Gates and verification ladder

Run bottom to top; each rung assumes the one below passed. Signal's public CI does not run
test-mock, so rungs 7 and 8 run locally on the Mac. **[amendment]**

| Rung | Command | Pass condition |
|---|---|---|
| 1 | `lake build Crdt.Merkle.<Module>` or `lake build Zrdt.<Module>` **[amendment]** | no errors, no `sorry` warnings for that module |
| 2 | `lake build` | "Build completed successfully", no new warnings |
| 2a | closure gate: `cd core && lake build` on a machine with no Mathlib, then `nm` on the linked `zrdtd` binary **[amendment]** | the build fetches nothing; `nm` shows no `initialize_mathlib*`/`initialize_Mathlib*` and no full `lean_initialize` call. Check the binary, not an archive: Lake links meta-imported objects too (B onward; `nm` from C) |
| 3 | `lake exe axiom_check` | prints `axiom gate passed: all checks pinned by #guard_msgs at compile time` |
| 4 | fresh clone: `make install && make run` | both succeed with no manual steps |
| 5 | `lake build Test.Differential` | all `plausible` properties pass (B onward) |
| 6 | `zrdtd` run over `vectors/vectors.json` (from `make vectors`), on Linux and on the Mac **[amendment]** | every reply matches its vector (C onward) |
| 7 | on the Mac: the TS stub and `zrdtd` run over the same vectors **[amendment]** | identical replies (C/D) |
| 8 | end-to-end on the Mac: four forks + evil server, `DEMO.md` beats 1–5 **[amendment]** | each beat's on-screen criterion (§8) met within its time |
| 9 | `make comparator` (Docker, Linux, `bwrap`) and `lake check` | both exit 0 (phase F only) |

Rung 3's `axiom_check` is a `lean_exe` rooted in `Test.Axioms`, which imports Mathlib, so building
it compiles and links Mathlib's C (review §1.1). It stays as it is: it is a default target, so
every `lake build` runs the gate; it runs on the Linux box only; it is outside `core/` and never
ships. **[amendment]** (lead to confirm)
**[amendment, 2026-11-01 late]** The `Test` library (which holds `Test.Axioms`) replaced
`axiom_check` in the default targets: every `lake build` still elaborates the gate, without
linking Mathlib's C (about half of a fresh `make install`). `lake exe axiom_check` still works;
`make run` re-runs the gate with `lake lean Test/Axioms.lean`.

Trusted at rung 9: Lean kernel (plus external checkers with `--paranoid` if time), the statements
in `Comparator/Challenge.lean`. Everything below the spec is covered by refinement. Everything
outside the proofs is listed in the README as trusted: the Lean compiler and runtime, the frame
codec and protobuf field scan (Lean, unproved, small), the TS client, and the host duties. There
is no C of ours and no external SHA-256. **[amendment]**

## 7. Risk register

| Risk | Impact | Mitigation / fallback |
|---|---|---|
| A Mathlib import leaks into `core/` **[amendment]** | `zrdtd` initialises and links all of Mathlib and the Lean compiler; the Mac build needs Mathlib | `core/` is its own package with no `require`; rule 12; the closure gate (rung 2a) on every merge that touches `core/`. |
| `Std.ExtTreeMap`/`ExtTreeSet` lemma coverage in v4.35 makes `Refine.lean` slow going **[amendment]** | B.Refine slips | Keep `Built` minimal; the prototype `rawAccept_built` is about 100 lines with core and Std only. Fallback: `Std.HashMap` with `Equiv`-form statements. Performance is fine for chat sizes either way. |
| Hash cycles in the model (a record linking its own digest) break naive statements | wrong theorem shapes | Already handled: the `CheckedStore` certificate is `AcceptBuilt`, which excludes cycles by construction; `fetched_union` is stated on head sets; salvage is stated via `AcceptBuilt`. Do not try to prove `Fetched s hs → Fetched s (heads s)`: it is false (two-record cycle). |
| `zrdtd` crashes, panics or runs out of memory **[amendment]** | nothing can be accepted | Fail closed: the host shows "zrdt unavailable" and marks nothing accepted. `LEAN_ABORT_ON_PANIC=1` turns a silent `panic!` into an exit. The decoder never sizes an allocation from an untrusted count (fuzz vector). On restart the host re-`OPEN`s from the SQL rows. |
| In-process `.node` (stretch only): the shipped Linux `libleanrt.a` cannot be linked into a `.node` (local-exec TLS) **[amendment]** | the stretch only | The stretch is macOS only, time-boxed to 2 h. It copies every output (Electron rejects external buffers) and guards every entry with an initialised flag. `zrdtd` is the shipped path. |
| Relay forgery: a member links a fake record in another member's name and serves it when asked **[amendment]** | a fake shown under a real member's name | Three-valued provenance: the fake shows "relayed by X" and never counts as the author's until `authorConfirmed`. Authors list records in their name that they did not create in `disown`, in every later message (never refuse them). Relayed messages never apply side-effect fields such as `profileKey`. The limit `relay_attribution_indistinguishable` is stated. |
| Privacy of stores and dumps **[amendment]** | content outlives Signal's delete and expiry rules; a dump leaves Signal's encryption | The store holds structure only. The opening (`zrdtOpening`) is marked `erase`. Each exported opening has field 15 (the group master key) removed, so no dump carries the master key; the commitment excludes that field, so the opening still checks. The exporter omits content of disappearing, deleted-for-everyone and view-once messages, gives later joiners structure only, and needs OS authentication and a "do not share" warning. No mirror or server transport unless the dump is encrypted. The README says that DAG metadata persists. |
| Signal-Desktop build at `v8.33.0` on the Mac (Electron 44.9.1, Node 24.22.0, pnpm 11.24.0) **[amendment]** | D slips | Checkpoint F0 on day 1, before any code change. Install Xcode Command Line Tools, Python 3, Node 24.22.0 and `pnpm@11.24.0` first. Electron's binary downloads lazily on first use. `NODE_APP_INSTANCE` needs `config/local-<name>.json`. The mock-server launch gives separate profiles and fake primaries, so no accounts are needed. |
| Mac access **[amendment]** | H1–H3 and F0 blocked; no GUI checks | This box's SSH key is not authorised on the Mac: add it (or enable Tailscale SSH), or run Claude Code on the Mac (§9 Q8). Launch Signal from the Mac's logged-in GUI session (Aqua, Keychain), not from a plain SSH session. |
| Mock-server fidelity: four desktops in one group, sender keys, `ciMode` **[amendment]** | E, D | `ciMode: 'full'` is required; set explicit demo timeouts for its shorter retries. Day-1 H3 spike: desktops exchange sender-key group messages through the mock. If a needed server feature is missing, add it to the mock (plain TypeScript) rather than switching villain. |
| Sealed sender hides who sent an envelope **[amendment]** | none for group messages | Not from the server: it infers the sender of a group message from the recipient set and from the sender's own `SyncMessage.Sent`. So `dropGroupMsg(alice, carol)` is a fair server rule. The mock holds every key, so the rules use only what a real server sees. (Certificate pinning and upstream acks only matter for the proxy stretch, APP.md §8b.) |
| Linux box disk **[amendment]** | Lean worktrees do not fit (18 GB free; a Mathlib checkout is 6.9 GB) | Extend the LV before creating Lean worktrees (`sudo lvextend`; a human approves it). |
| Demo time budget **[amendment]** | over 5 minutes | The five beats total ≤ 4 min, leaving time for the intro and the proof pitch (§8). Beat 5 is the doctored variant only, and `doctor.ts` runs on Bob's export automatically. Rehearse twice from cold (F4). |
| Time **[amendment]** | everything | **Hard fallback**: if checkpoint F2 is not green on day 3, start the mini-client on day 4 with a 2-day budget: a minimal Electron chat client over plaintext JSON, with the same `zrdtd`, the same `ts/zrdt/ui` and the same `demo/rules.ts` (through a small websocket relay adapter). The Lean deliverable, `zrdtd`, the villain rules and the five beats survive unchanged; only "on top of Signal" is lost. |
| Over-claiming **[amendment]** | credibility | Use the §1 pitch. Say "detect", never "prevent". A gap or "withheld" result shows that histories differ, not that the server is at fault. "Confirmed by" a live message means "held by the sender"; authorship needs `authorConfirmed`. `open` does not catch the removal or edit of a head, or an appended forgery. Never claim confidentiality of dumps. Cite Keybase as prior art. |

**Dated checkpoints** (the fallback gate; dated from day 1 until the deadline is known, §9 Q1)
**[amendment]**:

- **F0, day 1, on the Mac:** `pnpm install` and `pnpm run generate` at `v8.33.0`, and `pnpm start`
  shows the link screen; the `twoClients` mock test passes; the backend shows its kind and
  version; `zrdtd` completes one `ACCEPT` round trip inside the fork's Electron; `kill -9` on
  `zrdtd` shows the banner.
- **F1, day 2:** four desktops in "Camping" exchange messages; `dropGroupMsg` visibly drops one.
- **F2, day 3, go/no-go:** `demo/smoke.ts` (Playwright) passes: three sends, the same digests
  everywhere, and `MISSING` after a drop. If not green, start the mini-client on day 4 with
  2 days.
- **F3, day 5:** the relay and author-resend round trip, plus the gap and compare-code UI.
- **F4, day 6:** the backend is switched to `zrdtd`, and a cold-start rehearsal.

## 8. Demo acceptance criteria **[amendment]**

Four desktop instances (Alice, Bob, Carol, Dave) on the Mac mini, against one `EvilServer` with a
visible control panel, in one group ("Camping") of which all four are members from creation.
Alice's, Bob's and Carol's desktops have each sent one warm-up message, and rules are armed only
after that. Dave's desktop is linked just before beat 5 and sends nothing before its import.
**[amendment]**

1. **Codes match (30 s).** Alice, Bob and Carol exchange three messages. Bob copies his compare
   code; Carol pastes it. Visible: "identical".
2. **Gap (60 s).** Server: `dropGroupMsg(alice, carol)`. Alice sends; Bob sends a *plain* reply.
   Carol's screen shows a gap row above Bob's reply for 3–5 s (`ZRDT_RESEND_DELAY_MS`). Carol's
   app asks Bob; the message appears in place as "relayed by Bob"; then the author fast path makes
   it "confirmed by Alice". Visible: the gap row, the message filling it in place, then the label
   change, with no manual action.
3. **Withheld (45 s).** Server: `blackhole(carol)`. Alice sends; nobody replies. Carol's screen
   shows nothing wrong, and the demo says so (`withheld_tail_undetectable`). Bob copies his compare
   code; Carol pastes it. Visible: "Bob has 1 message you don't (·k7f2). Asked; no answer." Clear
   the villain; "Ask again" recovers it.
4. **Doctored restore (40 s).** In Carol's Settings → Internal, export the store. `doctor.ts`
   removes a **linked, non-head** record. Carol imports the file: `OPEN` fails. Visible: "message
   ·9ac1 is missing" (from the `missing` list); "Keep what verifies" loads the rest as `imported`.
   There is no on-disk edit (the DB is SQLCipher). Presented as "a tampered restore is caught",
   not as a server attack.
5. **Restore from anyone (60 s, doctored variant only).** See `RESTORE_PLAN.md` §6. Dave imports
   Bob's export, onto which `doctor.ts` automatically appended two fakes attributed to Bob on top
   of the genuine head. Visible: everything collapsed and grey. Alice writes: the genuine history
   becomes "held by Alice", and Alice's own messages "confirmed". Bob writes: Bob's genuine
   messages become confirmed, and the two fakes are marked "not confirmed by Bob".

The beats total ≤ 4 minutes (235 s), leaving time for the intro and the proof pitch within the
5-minute demo. "A stock client keeps working" is a stretch (phase E).

## 9. Open questions for the humans

1. **Deadline** and judging date. They set the dates of checkpoints F0–F4 (§7), which are counted
   from day 1 until then. **[amendment]**
2. **Signal accounts**: none are needed for the mock-server demo. For the proxy stretch against
   staging: who provides three numbers?
3. **Android**: attempt it at all? (Recommendation: no, unless desktop beats 1–5 pass with two days
   to spare.)
4. **SHA-256**: **decided**, pure Lean (§2). **[amendment]**
5. **Lean version**: **decided**, stay on v4.35.0 / Mathlib v4.35.0 for the whole project. Nothing
   in the build pipeline argues for a bump. Note that 4.35 prefixes exported symbols with the
   package name, so renaming a Lake package renames every init symbol. **[amendment]**
6. **Comparator**: is a Docker-based run acceptable to the judges, or do they run it themselves on
   Linux? Either way the challenge file is the deliverable.
7. **Fork repo**: name and hosting for `signal-desktop-zrdt` (a public fork of
   signalapp/Signal-Desktop at `v8.33.0`, built on the Mac mini). **[amendment]**
8. **Mac mini SSH access**: add this box's SSH key to the Mac's `~/.ssh/authorized_keys` (or enable
   Tailscale SSH), or run Claude Code on the Mac for lanes H1–H3? GUI checks need the Mac's
   logged-in session either way. **[amendment]**
9. **Demo machine**: is the Mac mini the demo machine (it needs a display at the venue), or does a
   MacBook run the same build? Is its chip and RAM enough for four Electron instances plus the
   mock server? **[amendment]**

## 10. Status snapshot (2026-11-01, wave 3) **[amendment]**

**zrdt repo** (branch `review/2026-11-01-plan-amendments`, `7f327ff`, plus wave 3 on
`build/w3-merge`): `lake build` is clean and runs the gate; `lake exe axiom_check` prints
`axiom gate passed`. Wave 3 Lean lane: `abs_accept` (`AcceptMeans`) also says outright that an
accepted record's links were all held and the record is in the new store; `Api.lean` has an
`agree` example across two accept orders; `committedBytes_idem` and `commitWithOpening_matches`
(`core/Zrdt/Commit.lean`) prove that `COMMIT`'s opening always passes the opening check; the gate
also pins these and some spec obligations.

- **Spec** (`Crdt/Merkle/`): `Defs`, `Integrity` (`fetched_agree`, `fetched_of_build`; the
  `_global` forms are gone), `Chat` (`fetched_build`, `fetched_union`, `acceptBuilt_union`,
  `acceptBuilt_insert`, `salvage_built`, `salvage_maximal`, `confirmed_exact`,
  `reach_implies_held`, `LiveFacts`, `authorConfirmed`, `foreignMarked`, `holders`, `status` with a
  single-holder `heldBy`, `HonestAuthor`, `authorConfirmed_sound`, the four limits), `LoadSpec`.
  `TaskList.lean` is deleted.
- **Proofs about the code**: `Bridge`, `Refine`, `EncodeProofs`, `LoadApi`, `Classify`,
  `ClassifyFast`, `ClassifyStatus`, and `Api.lean` with the eleven statements of §3.2. The gate
  pins exactly those names. No `sorry`, no `native_decide`.
- **Core** (`core/`, Init and Std only): `Digest`, `Sha256`, `Record`, `Encode`, `Store`
  (`CheckedStore`), `Commit`, `Provenance`, `Proto` (protocol 2: `ACCEPT` returns the record
  bytes, `COMMIT` the opening, `ACCEPT_RECORD` `0x10` with `BAD_OPENING`; blob count limit),
  `Vectors` (checked in `lake build`), and `zrdtd`. The closure check passes on the `zrdtd`
  built at `79e3dfa` and again on `build/w3-merge`. Wave 3 changed `core/` (the `COMMIT` lemmas),
  so `zrdtd`'s `VERSION` build id is now `26a279935e388ed8`; the fork's submodule is still at
  `79e3dfa`.
- **Comparator** (rung 9): `Comparator/Challenge.lean` (the 11 statements with `sorry`, not a
  default target), `comparator.json`, `make comparator`, `make check` and `make comparator-local`
  are written and have **not been run**. They re-check all of Mathlib and ran out of memory on
  the 63 GB Linux box; they run once, as the last step, with kejace's approval.
- **Not written**: `Test/Differential.lean` (rung 5), `proxy/` (stretch).

**Fork** (`l-adic/signal-desktop-zrdt`, branch `zrdt`, `eb895b411`; Mac checkout with the zrdt
submodule at `79e3dfa`): `ts/zrdt/` (service, backends daemon/stub/codec, scope, send, receive,
resend, ui, ci), SQL migration 1850, Redux slice `ducks/zrdt`, Settings → Internal
export/import/salvage, `demo/` (harness, launch, evil, rules, panel, doctor, smoke). `DEMO.md` is
still to write.

**Wave results.**

- First end-to-end run of `demo/smoke.ts` on the merged fork with the real `zrdtd`: **25/26 pass
  in 43 s.** Beats 1 to 3 work: equal compare codes; drop → gap row → recovery; blackhole →
  "Bob has 1 message you don't" → "Asked; no answer." → "Ask again" recovers; hold/release.
- **The one failure** (beat 2): the check that the recovered copy is first "relayed by Bob" never
  sees it. The author fast path upgrades it to live, "confirmed by Alice", too fast
  (`zrdtStatus` shows `wasRelayed: true`, provenance live). Wave 3 fixes it (fork lane: hold
  the fast path, or have the test accept a recorded relayed state). Beats 4 and 5 are not in the
  smoke test yet.
- Wave 3 (2–3 h): the beat 2 fix, beats 4 and 5 in the smoke test, `DEMO.md`, Comparator, this
  README and these documents. Results: the fork holds the author fast path for
  `ZRDT_AUTHOR_FASTPATH_DELAY_MS` (3 s in the demo harness), and beats 1 to 3 pass 26/26 with it;
  `demo/smoke.ts` covers beats 4 and 5 and passed 41/41 on its branch; `demo/DEMO.md` and a
  MacBook kit (`demo/pack.sh`, `demo/run-demo.sh`) are written. The merged fork branch is checked
  again before the demo. Comparator is written, not run.

History: phase 1 is `06192c1`; the plan documents `383a9fb`..`690ae65`; the review `52d9e15`
(merged in `e135eff`, PR #1); lanes L1 (`567c2be`), L2/L3 (`e2b3160`), T5 (`dcc2982`) and proofs
P1–P4 (`7f327ff`).
