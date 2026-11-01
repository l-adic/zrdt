# zrdt

A verified transcript-consistency layer for Signal group chats. Each message carries hash links
to the messages its sender had seen, and a verified Lean core checks them.

> A server cannot make a member's app accept a history with a hole in it: if any later message
> builds on one you lack, you are told, and your app asks for it. Two members can confirm with
> one code that they hold the same set of messages; once the server splits a group it can never
> merge it back without the gap showing. The server can still delay, hold back the newest
> messages until someone replies or members compare, and deliver concurrent messages in
> different orders.

Signal keeps messages secret and says who sent each one. zrdt adds completeness and consistency
of the history. The checks are written in Lean 4 without Mathlib, proved in Lean with Mathlib,
and compiled into `zrdtd`, a small program that runs beside a Signal-Desktop fork and checks every
record the fork sends or receives.

Lean v4.35.0, Mathlib v4.35.0. Plan and design: `docs/PLAN.md` (scope, contracts, gates),
`docs/PLAN_HUMANS.md` (the theorems in plain English), `docs/APP.md` (the Signal-Desktop fork),
`docs/RESTORE_PLAN.md` (restore from any member's copy).

## The idea

A **record** is four things: the chat id, a commitment to the message content, **links** (the
digests of the newest messages the sender held), and the author's Signal id (ACI). Its **digest**
is the SHA-256 of its encoding. A **store** holds the records of one chat. A record is accepted
only when every record it links is already held. The **heads** are the records nothing links
yet. Two members compare histories by comparing heads (the "compare code").

## How the pieces fit

```
  Crdt/Merkle/     spec (Mathlib): Record, Store, accept, heads, Reach, Fetched, AcceptBuilt, status
       |           and the proofs about the code: Bridge, Refine, LoadApi, Classify*, EncodeProofs
       |           Api.lean: the 11 advertised statements
  core/Zrdt/       the code that ships (Init and Std only, no Mathlib): Digest, Sha256, Record,
       |           Encode, Store (CheckedStore), Commit, Provenance (CLASSIFY), Proto, Vectors
  zrdtd            core/Zrdtd/Main.lean: frames on stdin/stdout, one table of CheckedStores
       |           u32 length | op | body   (protocol 2, core/Zrdt/Proto.lean)
  Signal fork      l-adic/signal-desktop-zrdt, branch zrdt (Signal-Desktop v8.33.0):
                   ts/zrdt/ (send, receive, resend, UI), zrdt/ submodule (this repo), demo/
```

The fork never computes a hash or heads, and never decides whether a record is accepted. It
chooses which messages are records, passes their bytes, and records how each one arrived. If
`zrdtd` exits, the fork shows "zrdt unavailable" and marks nothing accepted.

## What is proved

### About the shipped code

These are the only advertised results. They are in `Crdt/Merkle/Api.lean`, are stated about
`Zrdt.CheckedStore` (the type `zrdtd` holds), and are pinned by the axiom gate. `abs c` is the set
of records store `c` holds, seen in the spec model. "Or a collision" means two different records,
in the stores involved, have the same SHA-256 digest.

| Lean name | In plain words |
|---|---|
| `Zrdt.CheckedStore.fetched` | A store holds every record its heads reach, and nothing else. |
| `Zrdt.CheckedStore.no_collision` | No two different records in one store have the same digest. |
| `Zrdt.CheckedStore.agree` | Two stores with the same heads hold the same records. Or a collision. |
| `Zrdt.CheckedStore.abs_accept` | `ACCEPT` either adds the record exactly as the spec's `accept` says (every link of it was already held, and the record is now in the store) and returns its digest, or leaves the store unchanged and gives a true reason: the exact list of missing links, a collision, wrong chat, or too large. |
| `Zrdt.CheckedStore.abs_merge` | A merged store holds the records of both stores. |
| `Zrdt.CheckedStore.open_iff` | `OPEN` loads a saved copy exactly when it decodes, is within the size limits, has no collision, is all of this chat, and its records can be accepted one at a time in some order. The store then holds exactly those records. So a copy with its newest records removed, edited or added to still opens (see the limits below). |
| `Zrdt.CheckedStore.salvage_spec` | `SALVAGE` ("keep what verifies") keeps exactly what the spec's `buildRetry` keeps, and reports the digests of the rest, sorted. |
| `Zrdt.CheckedStore.encode_open` | Saving a store and opening it again gives back the same store. |
| `Zrdt.CheckedStore.confirmed` | If your store and a sender's store both hold the records a live message links, what those links reach is the same in both. Or a collision. This says the sender holds them, not who wrote them. |
| `Zrdt.CheckedStore.classify_spec` | `CLASSIFY` gives each stored record exactly the spec's label: confirmed by its author, not confirmed by its author, held by one member (the smallest ACI among the other members whose live messages reach it), or unconfirmed. |
| `Zrdt.encode_injective` | Different records have different encodings, with no size bound. So a collision above is a collision of SHA-256, not of the encoding. |

Each statement has a concrete example next to it in `Api.lean` with every hypothesis discharged,
and examples that show it rejects bad stores.

What the statements mean depends on these definitions (read them to check the claims): `abs`,
`toSpec`, `hashSpec` (`Bridge.lean`); `specOf`, `AcceptMeans` (`Refine.lean`); `accept`,
`digests`, `heads`, `Reach`, `Fetched`, `CollisionIn` (`Defs.lean`); `AcceptBuilt`, `buildRetry`,
`status`, `liveRecords`, `authorConfirmed`, `foreignMarked`, `holders` (`Chat.lean`); `liveOf`
(`Classify.lean`); `Status.toSpec` and the byte order on `Aci` (`ClassifyStatus.lean`);
`WellSized`, `decodeBlob`, `encode` (`core/Zrdt/Encode.lean`).

### The spec theorems behind them

These are proof obligations, not results on their own. They are about plain finite sets of
records and any hash function.

- `fetched_agree` (`Integrity.lean`): two stores fetched from the same heads are equal, or collide.
- `fetched_of_build` (`Integrity.lean`): a store built by accepting records one at a time is
  fetched from its own heads, or collides. `fetched_build` (`Chat.lean`) says the same for an
  accept-built store.
- `fetched_union`, `acceptBuilt_union`, `acceptBuilt_insert` (`Chat.lean`): merging and accepting
  keep a store valid.
- `salvage_built`, `salvage_maximal` (`Chat.lean`): salvage keeps an accept-built store, and the
  largest one. `LoadSpec.lean`: what salvage keeps lies inside every store that takes in the copy.
- `confirmed_exact`, `reach_implies_held` (`Chat.lean`): a live message's links reach the same
  records in your store and the sender's; a sender holds what its message reaches.
- `authorConfirmed_sound` (`Chat.lean`): if an author's app disowns every record in its name it
  did not write (`HonestAuthor`), then every record "confirmed by" that author was written by it,
  or two records collide.

### Four limits

What links alone cannot do. Each is a concrete case in `Chat.lean`, checked by `decide`, and each
is why some part of the app exists.

- `withheld_tail_undetectable`: a phone missing only the newest message passes every local check.
  Remedy: the next message that links it, or a compare code.
- `tail_replaced_passes_open`: a copy whose newest records were replaced by a consistent fake
  opens. So does a copy with its newest records cut off, or with made-up records added on top:
  `OPEN` only checks that every link resolves. It catches a record cut out or changed when
  another record links it. Remedy: live messages; nobody's live message reaches the fake.
- `gap_indistinguishable`: "the server withheld it" and "the sender linked a made-up digest" look
  the same. A gap shows two histories differ; it does not show who is at fault.
- `relay_attribution_indistinguishable`: without disown lists, a relayed record's author cannot
  be checked. Remedy: the author's app disowns what it did not write.

### Axioms and the gate

`Test/Axioms.lean` pins the axioms of each of the 11 names to `propext`, `Classical.choice`,
`Quot.sound` with `#guard_msgs`. It is a default target, so every `lake build` runs it, and any
`sorry`, `native_decide` or new axiom fails the build. It also pins some proof obligations that
are not advertised: `authorConfirmed_sound`, `salvage_maximal`, `confirmed_exact`,
`fetched_union`, and facts about openings (`openingMatches_spec`: what a matching opening means;
`Zrdt.Proto.acceptRecord_accepted`: `ACCEPT_RECORD` checks the bytes and the opening before it
stores; `committedBytes_idem`, `commitWithOpening_matches`, `Zrdt.Proto.commit_openingMatches`:
the opening `COMMIT` returns always passes that check). Nothing that `lake build` builds has a
`sorry`, a `native_decide`, an `axiom`, an `opaque` or an `@[extern]`. The only `sorry`s in the
repository are in `Comparator/Challenge.lean`, on purpose: it restates the 11 statements with
`sorry` proofs as the challenge for `lake comparator`, and it is not a default target. Concrete
examples use `decide +kernel`, which adds no axiom. (The gate also pins older CRDT results in
`Crdt/*.lean` that are not part of the chat claims.)

**Comparator: not run yet.** `comparator.json` names the 11 statements and permits only the
three axioms above; `make comparator` would judge `Crdt.Merkle.Api` against
`Comparator/Challenge.lean` with `lake comparator`, and `make check` would replay the build with
`lake check`. Neither has completed a run: they re-check all of Mathlib, and the attempts so far
ran out of memory on a 63 GB machine. They run once, as the last step, only with the
maintainer's approval. Until then the statements are checked by reading `Api.lean`, and the
axioms only by the gate above, which runs in the elaborator during `lake build`.

## Trusted base

Not proved, and needed for the claims to hold of the running app:

- **The Lean kernel**, which checks every proof during `lake build`. No independent re-check
  (`lake comparator`, `lake check`, `leanchecker`) has been run yet (see above).
- **The Lean compiler and runtime.** The proofs are about the Lean code; `zrdtd` is that code
  compiled by Lean's standard `lean_exe` link. There is no C of ours.
- **The frame codec and the main loop** (`core/Zrdt/Proto.lean`, `core/Zrdtd/Main.lean`). Lean,
  unproved, small. `vectors/vectors.json` pins every op and reply.
- **The protobuf field scan and the commitment** (`core/Zrdt/Commit.lean`). Lean, small. It
  reads the top level of a `DataMessage` and removes fields 15 and 200 before hashing. What it
  keeps is not proved against a protobuf parser. Proved: removing the fields again changes
  nothing (`committedBytes_idem`), and the opening `COMMIT` returns always matches its commitment
  (`commitWithOpening_matches`).
- **SHA-256** (`core/Zrdt/Sha256.lean`) is pure Lean, checked against the NIST examples, not
  proved equal to FIPS 180-4. The theorems hold for whatever it computes; a collision is never
  assumed away, it is reported.
- **The TypeScript client** in the fork: it passes the right bytes, applies the scope predicate
  (which messages are records), and talks to `zrdtd`.
- **Host duties.** The fork marks each record live, relayed or imported, and keeps the disown
  lists of live messages. These are the "live facts" `CLASSIFY` reads; if they are wrong, the
  labels are wrong. The UI wording is also the host's.

## Not proved, not claimed

- Who wrote a record, beyond `authorConfirmed`. Records carry no signatures. Signal authenticates
  the sender of each live message; a relayed or imported record counts as its author's only once
  the author's own live message confirms it.
- Who is at fault for a gap. A member who links a made-up digest, or an author who is offline,
  looks the same as a server that drops messages.
- That SHA-256 resists collisions. The theorems only say a disagreement points to a collision.
- Delivery. The server can go silent, delay, or hold back the newest messages until someone
  replies or members compare.
- Confidentiality (Signal's job). An exported store leaves Signal's encryption. Links are
  receipts the whole group sees.
- Membership changes after the chat starts, edits, deletes, reactions, polls, 1:1 chats, time,
  and compaction (a store only grows).

## Quick start

```
make install && make run
```

Prerequisites: [elan](https://github.com/leanprover/elan) (`curl https://elan.lean-lang.org/elan-init.sh -sSf | sh`;
it installs the Lean toolchain named in `lean-toolchain`), python3, git and curl. `make install`
fetches the Mathlib build cache, runs `lake build` (proofs and axiom gate) and builds `zrdtd`;
about 10 minutes on a 32-core machine from a fresh clone, most of it compiling Mathlib's C code
for the `axiom_check` executable (the cache has the proofs, not the native objects). `make run` runs the axiom gate, replays the 133 test vectors
against `zrdtd` and round-trips a 1000-record chat through it. The GUI demo (Signal Desktop with
zrdt) is in `l-adic/signal-desktop-zrdt`: `make install && make run` there.

## Build and check

```
make install            # fetch the Mathlib cache, lake build (runs the axiom gate), build zrdtd
make run                # axiom gate, the 133 test vectors and a 1000-record smoke against zrdtd
lake build              # build the spec and proofs; the axiom gate runs as part of it
lake exe axiom_check    # prints "axiom gate passed: ..."
cd core && lake build   # the shipped code and zrdtd only: Init and Std, no Mathlib
make vectors            # regenerate vectors/vectors.json (its checks run in `cd core && lake build`)
python3 vectors/zrdtd_client.py vectors core/.lake/build/bin/zrdtd   # zrdtd gives every reply
make closure            # zrdtd links no Mathlib; silent if OK
make comparator         # NOT RUN YET: run once, at the end, with approval (see above)
```

**Running Comparator.** `make comparator` builds `Comparator.Challenge` and runs the official
comparator on `comparator.json`, in one of two forms (`COMPARATOR=builtin|standalone`; the
default, `auto`, takes the first that can run here):

- **builtin**: `lake comparator --config comparator.json`, built into Lake since Lean v4.35.0
  (this toolchain) and the form upstream recommends. It sandboxes the build with bubblewrap,
  which needs unprivileged user namespaces. On Ubuntu 23.10 and later AppArmor blocks those:
  `bwrap --ro-bind / / true` fails with `setting up uid map: Permission denied` (it does on our
  Ubuntu 24.04 machine). The fix needs root; give bwrap a profile that allows `userns`:

  ```
  printf 'abi <abi/4.0>,\ninclude <tunables/global>\nprofile bwrap /usr/bin/bwrap flags=(unconfined) {\n  userns,\n}\n' \
    | sudo tee /etc/apparmor.d/bwrap && sudo apparmor_parser -r /etc/apparmor.d/bwrap
  ```

  (or, for the whole machine, `sudo sysctl kernel.apparmor_restrict_unprivileged_userns=0`).
- **standalone**: `leanprover/comparator`, archived when it moved into Lake, sandboxed with
  landrun (Landlock, no user namespaces, no root). `make comparator-tools` fetches and builds,
  into `.tools/`, its last commit (on Lean v4.35.0), the `lean4export` that commit pins (built
  with the same Lean, as the export format requires) and landrun from `main` (needs Go; Go 1.21
  or newer fetches the Go 1.24 that landrun asks for). It runs nothing. `make comparator` then
  runs `lake env <comparator> comparator.json` as comparator's README asks, in a
  `systemd-run --user` service with `RestrictAddressFamilies=~AF_UNIX`.

Either form re-checks all of Mathlib and has needed over 60 GB, so it runs with `MemoryMax=48G`
and `MemorySwapMax=0` under `systemd-run --user` where available (`MEMORY_MAX=...` to change).
`make install` and `make run` never run it. Status: not run yet.

`make help` lists the targets. `make zrdtd` builds the daemon at `core/.lake/build/bin/zrdtd`.

## The demo in five beats

Four desktops (Alice, Bob, Carol, Dave) in one group, "Camping", against an "evil server":
Signal-Desktop's own mock server with its delivery hooks overridden, driven from a control
panel. The script is `demo/DEMO.md` in the fork (`l-adic/signal-desktop-zrdt`, branch `zrdt`);
`demo/README.md` there explains the harness.

1. **Codes match.** Three messages; Bob's compare code pasted on Carol's side: "identical".
2. **Gap.** The server drops Alice's message to Carol. Bob replies. Carol sees a gap row, her app
   asks Bob, the message appears in place as "relayed by Bob", then "confirmed by Alice".
3. **Withheld.** The server withholds Alice's message from Carol and nobody replies. Carol sees
   nothing wrong (`withheld_tail_undetectable`). After pasting Bob's code: "Bob has 1 message you
   don't. Asked; no answer." "Ask again" recovers it once the server relents.
4. **Doctored restore.** A record that a later record links is cut out of Carol's exported
   store. Import fails: "message ·9ac1 is missing". "Keep what verifies" loads the rest.
5. **Restore from anyone.** Dave imports Bob's export, with two fakes in Bob's name added on top.
   Everything starts grey. Alice writes: the genuine history becomes "held by Alice". Bob writes:
   his messages are confirmed, and the fakes are marked "not confirmed by Bob".

Status (2026-11-01, wave 3): the smoke test (`demo/smoke.ts`) now covers all five beats with the
real `zrdtd`. On the wave 3 fork branches it passed 41 of 41 checks (beats 1 to 5), and 26 of 26
for beats 1 to 3 with the author fast path held back by `ZRDT_AUTHOR_FASTPATH_DELAY_MS` (3 s in
the demo harness), so "relayed by Bob" stays on screen for about 3 s before "confirmed by Alice".
The merged demo build is checked again before the demo.

## Layout

```
Crdt/Merkle/   Defs, Integrity, Chat (spec); Bridge, Refine, LoadSpec, LoadApi, Classify,
               ClassifyFast, ClassifyStatus, EncodeProofs (proofs about the code); Api (results)
Crdt/*.lean    phase 0: CRDT merge algebra (not part of the chat claims)
core/          package zrdt-core: Zrdt/* and Zrdtd/*; no `require`, builds without Mathlib
Test/          Axioms.lean, the axiom gate
Comparator/    Challenge.lean: the 11 statements with `sorry`, the challenge for `lake comparator`
               (comparator.json); not a default target, not run yet
vectors/       vectors.json (generated) and zrdtd_client.py
docs/          PLAN, PLAN_HUMANS, APP, RESTORE_PLAN, review-2026-11-01/
```
