# Review of PLAN.md and APP.md: the C parts and the Signal integration

Date: 2026-11-01. Scope: PLAN.md §2–§10 and APP.md in full, focused on (a) Lean → C → host and
(b) the Signal Desktop fork, wire format, villain and demo.

**How this was produced.** Nine independent reviewers, one per dimension. They checked claims
against a shallow clone of Signal-Desktop `main` @5dad34ad (2026-10-28) and the `v8.33.0` tag, the
pinned Lean v4.35.0 toolchain (sources, libraries, `lean.h`), and real build spikes. The spikes
included a Lean library loaded as an N-API addon in Node 24.22.0, Electron-as-Node 45.0.0 and an
Electron 45 renderer preload. Eight further verifiers then tried to refute every serious finding by
reproducing it themselves. Result: 72 findings checked, **40 confirmed, 32 partly right
(corrected below), 0 refuted**. Severities in this document are the post-verification ones.
The spike sources are kept outside the repo (`~/devel/zrdt-review-spikes` on the reviewer's machine); see the appendix.

---

## 0. Bottom line

The plan's overall shape is sound:

- a Lean core with refinement proofs;
- the host only passes bytes;
- links travel inside Signal's encryption;
- the mock server is used as the villain.

Many specific claims hold (§6). But the C layer as written does not build. The recovery design
also lets one group member post messages under another member's name. And several demo beats
cannot happen as scripted. The changes, in priority order:

1. **Split the Lean code into a Mathlib-free library.** (Blocker, confirmed.) As planned, the
   compiled library would initialise and link all of Mathlib and the whole Lean compiler. (§1.1)
2. **Run libzrdt as a separate process (`zrdtd`) instead of an in-process N-API addon.** The
   shipped Linux Lean runtime cannot be linked into any `.node` at all. The alternatives work but
   cost more and put a crash-prone runtime inside Signal's window. (§1.2, §1.3)
3. **Use a pure-Lean SHA-256.** It is fast enough, kernel-checkable, and removes C from the
   trusted base. (§1.5)
4. **Fix four theorem statements** before Phase B starts: `decode_encode`, `encode_injective`,
   `abs_accept` with `inv_decode`, and the order instances `encode` needs. All are false or
   unprovable as written. (§1.6)
5. **Only the author re-sends message content.** Today any member can relay a record "from
   Alice", and Signal's sender authentication is bypassed. Reuse Desktop's sendLog/SavedProto
   path for resends and delete `ZrdtResend`. (§2.5)
6. **Hook into the right places in Signal.** On send, freeze the record once inside
   `sendNormalMessage`. On receive, change `MessageReceiver`. Hash the wire bytes, not rebuilt
   fields. Apply one scope predicate on both sides. Persist in dedicated SQL tables, not
   `items`. (§2.2–§2.7)
7. **Payload = salted commitment.** Otherwise the append-only store keeps plaintext that should
   have disappeared or been deleted. (§2.8)
8. **Rewrite Beats 1–4** so each can actually happen, and hook the villain at
   `handleMessage` / `prepareMultiDeviceMessage`. (§3)
9. **Narrow the pitch** to what is proved and shown. (§4)
10. **Add a day-1 environment block** that needs human approval: this machine cannot run Signal
    Desktop yet, and has 18 GB of free disk. Replace the fallback gate with dated, scripted
    checkpoints. (§5)

---

## 0a. Update: Signal Desktop is built and run on the Mac mini

**Decision (user, 2026-11-01).** The fork is built and run on the Mac mini (macOS), not on the
Linux dev box. Effects on this review:

- **Linux blockers leave the Signal critical path.** §5.1's libasound, libpulse, xvfb,
  chrome-sandbox and headless-flag issues no longer block the fork. The Linux box keeps the Lean
  work (Mathlib proofs, the gate, Comparator). Its disk problem (§5.1) still applies to the Lean
  worktrees.
- **Native artifacts are built on the Mac.**
  - Lean v4.35.0 publishes `darwin_aarch64` and `darwin` toolchains, and Electron 44.9.1 has a
    `darwin-arm64` build (both checked: HTTP 200).
  - There is no cross-compilation, so `zrdtd` (or a `.node`) must be built on the Mac with the
    Mac toolchain.
  - Put `Zrdt/` and `zrdtd` in their **own Lake package** with no `require mathlib` (e.g.
    `core/`, required by the root package). Otherwise `lake build zrdtd` on the Mac still clones
    Mathlib and its dependencies when it resolves the workspace (likely; not checked). With the
    split, the Mac needs only the toolchain, and building takes seconds.
- **Architecture (decision 1).**
  - The Linux TLS blocker (§1.2) very likely does not apply on macOS. Mach-O ignores
    local-exec TLS; this rests on cross-compile evidence, not a test on a Mac.
  - Mach-O's two-level namespace makes the libuv interposition problem (§1.4) unlikely.
  - So in-process N-API with the shipped static runtime is cheaper on the demo platform than the
    Linux analysis suggested.
  - The other reasons for `zrdtd` still hold: crash isolation and fail-closed behaviour, no
    hand-written C wrapper, all call sites already async, less effort.
  - **Recommendation unchanged (`zrdtd` first),** but the 2-hour N-API time box in the day-1
    spike (§1.3) now runs on the real target. If it passes, N-API becomes a real option rather
    than a stretch.
- **Day-1 checks on the Mac** (they replace §5.1 for the fork):
  - Install Xcode Command Line Tools, Python 3, Node 24.22.0 and `pnpm@11.24.0`. Node-gyp builds
    `mute-state-change`'s `addon.mm`, which is real code on macOS.
  - Launch Signal from the Mac's logged-in GUI session (Terminal or Screen Sharing), not from a
    plain SSH session. Electron windows need the Aqua session, and Desktop's DB key goes through
    `safeStorage`, which uses the login Keychain; that is normally locked in SSH sessions.
    Check whether the mock launch touches the Keychain at all.
  - Signing and Gatekeeper do not matter for an unpackaged dev launch, and the arm64 linker
    ad-hoc signs `zrdtd`.
- **Agent access.** The Mac resolves over Tailscale as `macmini.beefalo-decibel.ts.net`, but this
  Linux box's SSH key is not authorized there (`Permission denied (publickey,…)`). Either add the
  key to the Mac's `~/.ssh/authorized_keys` (or enable Tailscale SSH), or run Claude Code on the
  Mac for lanes H1–H3. GUI checks such as screenshots need the GUI session either way.
- **Still open:** the chip and RAM (three Electron instances plus the mock server), and whether
  the Mac mini is also the demo machine (it needs a display at the venue) or a MacBook runs the
  same build.

---

## 1. The C parts

### 1.1 Blocker: the compiled closure must be Mathlib-free

PLAN §3.1 and §4 B put `Hash/Encode/Impl/Ffi` in `Crdt/Merkle`. They are built on the spec
`Record`, and `Defs.lean` imports Mathlib.

- **Initialisers.** Every generated module initialiser calls the initialisers of all non-`meta`
  imports (`EmitC.lean:1007-1046`). Mathlib imports `Lean`, so its closure calls the full
  `lean_initialize()` and needs `libLean.a` (298 MB). Even `Mathlib.Order.Defs.LinearOrder`
  pulls in `Lean`.
- **Static facet.** `lake build Crdt:static` archives only the library's own modules
  (`Lake/Build/Library.lean:58`). Every Mathlib symbol would stay unresolved.
- **Mathlib cache.** `lake exe cache get` ships `.c` but no `.o` (`Cache/IO.lean@v4.35.0`). So
  `make lib` would compile roughly 370 MB of Mathlib C.
- **Module system.** It does not help. A private `import` used only in proofs still initialises
  the imported module at runtime. A `meta import` skips that, but the imported names cannot
  appear in public theorems or computable defs (reproduced).

For scale: an executable that imports only `Lean` is 118 MB with 63 MB RSS. The Mathlib-free spike
is 5.2 MB with 19 MB RSS.

**Change PLAN §3.1, §4 B and §4 C to two libraries:**

```
Zrdt/   (imports Init/Std only; this is what is compiled and shipped)
  Sha256.lean Digest.lean Record.lean Encode.lean Impl.lean Proto.lean Ffi.lean Vectors.lean
Zrdtd/Main.lean           lean_exe zrdtd  (Mathlib-free closure)
Crdt/   (Mathlib; imports Zrdt)
  Merkle/Defs Integrity Chat  EncodeProofs (encode_injective about Zrdt.encode)  Refine
```

- **Rule for PLAN §5:** no file under `Zrdt/` imports Mathlib or `Crdt`.
- **Gate:** add a closure check to `make lib`. It must print nothing:
  `nm -u <lib>.a | grep -oE ' U initialize_[A-Za-z0-9_]+' | sort -u | grep -vE 'initialize_(Init|Std|zrdt_Zrdt)'`
- **Theorems.** Theorems about `Zrdt` definitions live in `Crdt`. That is still "proofs about
  the code", not about a copy.
- **Statement consequences.** These need lead sign-off under rule 4:
  - an implementation record `Rec` with a canonical (strictly sorted, deduplicated) link array;
  - `toSpec : Rec → Record` and a spec-side hash;
  - canonicity added to `Inv`;
  - a lawful bytewise linear order on `Digest`. `Finset.sort` needs `IsTrans`, `Antisymm` and
    `Total`. Core 4.35 has no `Ord`/`LawfulBEq ByteArray`, so `Digest` must derive its own.
    `List.toFinset_sort` is the bridge lemma.
  - Estimate: about half a day.
- **Existing `axiom_check` exe.** Any `lean_exe` rooted in a Mathlib module also compiles and
  links Mathlib's C. Check that this is acceptable, or keep it interpreter-only.

### 1.2 Linux: the shipped Lean runtime cannot go into a `.node`

The toolchain's `lib/lean/libleanrt.a` is built with `-ftls-model=local-exec`: 307
`R_X86_64_TPOFF32` relocations. The `initial-exec` variant is not shipped (lean4
`src/runtime/CMakeLists.txt:98-107`). The bfd, lld and gold linkers all refuse it in `-shared`.
A `.node` is a shared object, so "libzrdt.a + runtime in binding.gyp" (APP §2) fails on Linux,
the plan's reference platform.

- **Lake has no fix.** On Linux, Lake's `:shared` facets and `precompileModules` deliberately
  leave Lean symbols unresolved (plugin model; `Lake/Build/Common.lean:1036`).
- **`linux_aarch64` has the same problem.** That matters if "Linux (Docker)" runs on Apple
  Silicon.
- **macOS is very likely fine.** Mach-O ignores local-exec; checked by cross-compiling, not on a
  Mac.

Three verified ways around it:

| Option | Result | Cost |
|---|---|---|
| A. Link the `.node` against `libleanshared.so` (APP §2 already names it) | Works in Node and Electron 45. `-Bsymbolic`, so no libuv/GMP interposition. | 231 MB `.so` (162 MB stripped), +24–36 MB RSS |
| B. Rebuild the runtime from lean4 @eb6cafb with `-fPIC -ftls-model=global-dynamic` | 40 s build. 5 MB self-contained `.node`, 0.8 ms load, 1.8 ms init, 9 MB RSS. Works in an Electron 45 renderer. | Must stay in sync on every Lean bump: lean4 tag, mimalloc v3.4.5 (= `MI_MALLOC_VERSION` 30405 in `lean.h`), libuv 1.48 and gmp 6.3 headers, `MIMALLOC_OPTS`. Built with g++, which upstream does not test. Recipe: `pic-runtime/build_rt_pic.sh` in the kept spikes |
| D. Separate process (§1.3) | Standard `lean_exe` link, libc-only, identical on Linux and macOS | A frame protocol and process supervision |

PLAN §7 row 1's day-1 spike ("export one function, call it from a C `main` and from Node") would
**not** catch this: a C `main` links fine. The C stub (APP §2) would not catch it either, because
it contains no Lean runtime. The failure would first appear at "D.swap", on the critical path.

### 1.3 Recommended architecture: one Lean dispatcher, `zrdtd` as the transport

The two reviewers disagreed (in-process N-API with option B, versus a daemon). The judge and the
verifier both recommend the daemon:

- **Synchronous calls buy nothing.** Every call site is already async: the send job in
  `conversationJobQueue`, the receive work in `conversation.queueJob`, and SQL over
  `ipcRenderer.invoke`.
- **The UI needs no synchronous answers either.** It renders values stored at accept time
  (digest, status, gaps, seen-by, fork marker). Redux selectors are memoised, so that precompute
  is needed anyway.
- **Measured round trips:** 10 ms to the first reply and about 55 µs per sequential round trip
  from an Electron 45 renderer preload. From Python it is about 14 µs.
- **The main window can spawn processes.** It runs with `sandbox:false`
  (`app/main.main.ts:725-728`), so the preload can use `node:child_process`. Spawning from the
  main process with `ipcMain.handle` (like `app/sql_channel.main.ts`) is also fine, and survives
  renderer reloads.
- **Crashes stay outside Signal.** In-process, a Lean stack overflow aborts the whole renderer
  (exit 134). V8 already owns SIGSEGV, so Lean leaves it alone. A `panic!` silently returns
  `default`, and an OOM calls `exit(1)`. Out of process, all of these become "the daemon
  exited", which is easy to make fail-closed.
- **No hand-written C** in the trusted base if SHA-256 is pure Lean.
- **Effort:** about 1–1.5 days, against 3–4 days with a long tail for N-API on Linux.

Design (verified in the `one-dispatcher` spike):

```lean
initialize stores : IO.Ref (Std.HashMap String ChatStore) ← IO.mkRef {}
def handle (req : ByteArray) : IO ByteArray      -- the only entry point
def main : IO Unit                               -- zrdtd: u32 len ‖ request frames on stdin/stdout
@[export zrdt_l_call] def call := handle         -- optional in-process stretch: ~20 lines of C, no store handles
```

- **Frame ops** replace the C header in PLAN §3.3, keyed by `conversationId`:
  `VERSION` (git hash of the Lean build), `OPEN(id, blob?) → check`,
  `ACCEPT(id, wireBytes|payload, links, author) → accepted|missing|collision`,
  `HEADS`, `HAS`, `REACHES`, `GET`, `ENCODE`, `CLOSE`. Outputs are sorted (§1.6).
- **Host side:**
  - `ts/zrdt/ZrdtBackend.std.ts`: one async interface.
  - `backends/daemon.node.ts`: spawns `$ZRDT_DAEMON` with `LEAN_ABORT_ON_PANIC=1`.
  - `backends/stub.node.ts`: the day-1 TypeScript stub, which replaces `ffi/zrdt_stub.c`.
  - The daemon's `exit` means a "zrdt unavailable" banner and nothing is marked accepted. On
    restart, re-`OPEN` from the persisted records.
  - `ZRDT_REQUIRE_LEAN=1` refuses the stub.
- **Bug to fix from the spike.** The read loop must loop until it has `n` bytes. `IO.FS.Stream.read`
  can return short reads, and the spike's `Zv.lean` loop does not handle them.
- **Gates.** Rung 6 becomes `zrdtd` run over `vectors.json`. Rung 7 runs the vectors through the
  TS stub and through `zrdtd` and diffs them. The gate's current path (`cd native && npm test`)
  does not exist, and it tests under Node rather than Electron.
- **Pitch wording.** It becomes "the verified core runs beside Signal and decides every
  acceptance". README's trusted base then lists: the Lean compiler and runtime, the frame codec in
  Lean (not proved, but small), the TS client, and the host.

**Day-1 spike** (half a day; unblocks all lanes): `Zrdt/Proto.lean` with
`VERSION/OPEN/ACCEPT/HEADS`, plus `lean_exe zrdtd` built on Linux x86_64 and macOS arm64. In the
fork, the backend interface, both backends, and `backend.kind`/`version` shown on screen. Pass
criteria:

1. One `ACCEPT` round trip works inside the fork's Electron.
2. `kill -9` on the daemon brings up the banner.
3. The stub is refused when `ZRDT_REQUIRE_LEAN=1`.

Optional, time-boxed to 2 h: on macOS, link the shipped `libleanrt.a` plus `zrdt_l_call` into a
`.node`, to keep the in-process stretch alive.

### 1.4 If in-process N-API is kept anyway (stretch)

All of these are verified:

- **Copy every output.** Electron 45/44 rejects external buffers with
  `napi_no_external_buffers_allowed` (22); Node 24 allows them. Use `napi_create_buffer_copy`,
  then free.
- **Hide symbols** when libuv is statically inside the `.node` (option B). Use
  `-Wl,--exclude-libs,ALL`, a version script exporting only `napi_register_module_v1`, and
  `-Bsymbolic`. Otherwise `uv_*` binds to Node's copy, and Lean's init drives Node's main loop
  from a second thread. Lake `:static` objects are built with `LEAN_EXPORTING`, so every
  `initialize_*`/`lp_*` symbol is exported unless it is hidden.
- **Guard and serialise every entry point.**
  - Every `zrdt_*` call checks an initialised flag. Calling an export before init dumps core in
    both Node and Electron.
  - `zrdt_init` is idempotent and protected by a mutex. The runtime's guard is a non-atomic
    static.
  - All calls are serialised process-wide. Refcounts are non-atomic, and merged stores share
    objects.
  - `lean_initialize_thread` is exported but not declared in `lean.h`. It does not give foreign
    threads stack-overflow detection.
- **Ownership.** `@[export]` rejects `@&`: every argument is consumed. Call `lean_inc` before a
  read-only call and hand the store over on accept, so it stays at rc = 1 and updates in place.
  Otherwise every accept copies the map: 16k inserts take 1,350 ms instead of 2.5 ms.
- **Lazy binding fails silently.** A `.node` with an unresolved symbol loads fine and kills the
  process at the first call. Gate it with `nm -D --undefined-only` against an allow-list.
- **`packages/mute-state-change` is not a usable template.** It is a single `addon.mm`, builds
  only on macOS (a `noop` target elsewhere), and its JS wrapper turns load failures into no-op
  stubs, which would make zrdt fail open. No in-tree workspace addon compiles real code on Linux.
- **Missing fork wiring:** a `rolldown.config.ts` `external` entry, `package.json` `build.files`
  (like lines 638-639), and `asarUnpack` (already covers `**/*.node`).
- **The "Electron native module ABI" risk (PLAN §7) is misframed.** Node-API is ABI-stable, and
  an addon built against Node headers loads in Electron unchanged. The real risk is embedding the
  Lean runtime.

### 1.5 SHA-256: choose pure Lean (answers PLAN §9 Q4)

The `pure-lean-core/Sha256.lean` spike, about 70 lines:

- passes the NIST vectors with `#guard`;
- runs at about 9 µs per 201-byte record and 31 ms per MiB compiled;
- can even be checked by the kernel (`decide +kernel`, about 2 s per block, axioms
  `[propext, Quot.sound]`).

`opaque sha256` with `@[extern]`, by contrast:

- **Cannot be `#eval`'d.** The interpreter looks up `l_sha256`, not the C symbol. Every
  hash-dependent `#eval`/`#guard` in Phase B (`hashRecord`, `accept`, `check`, `decode`) fails
  unless a `precompileModules` + `moreLinkArgs` workaround is used (it works with TOML).
- **Cannot be reduced by the kernel.**
- **Adds no axioms**, so the axiom gate cannot see the C trust. That contradicts the README's
  "no `opaque` contracts".

A middle option (`@[extern] def sha256 := leanSha256`) keeps kernel evaluation, but `#eval` still
fails and the C stays trusted.

### 1.6 Theorem statements in PLAN §4 B that are false or unprovable as written

| Statement | Problem (verified) | Fix |
|---|---|---|
| `decode_encode : Inv c → decodeStore (encodeStore c) = .ok c` | `=` on `Std.HashMap`/`HashSet` compares bucket arrays. Two stores with equal contents but a different insertion history differ, and both satisfy `Inv`. 4.35 has content-`BEq`/`Equiv` but no `DecidableEq`. The `Std.TreeMap` fallback in PLAN §7 has the same problem (insertion order changes the root). | State it via `abs`: `abs <$> decodeStore (encodeStore c) = .ok (abs c)` (or `Equiv`) |
| `encode_injective : Function.Injective encode` | ByteArray and `Finset` sizes are unbounded in Lean's logic, so a u32 length wraps. A concrete counterexample exists: a 2^32-byte payload against 2^27 crafted links. | Prove `InjOn` over `WellSized` records; have `accept` and `decode` reject oversize records. Or use self-delimiting lengths. |
| `abs_accept … ∧ Inv c'` together with `inv_decode` | `Inv` lacks `Closed`, and `inv_decode` grants `Inv` to stores that are not closed. With incremental heads, `Inv c'` then cannot be proved. The Lean model gives a counterexample. | Add `Closed` to `Inv` and merge decode with check (decode returns only checked stores), or make accept recompute heads |
| `encode` sorting `links : Finset Digest` | `Finset.sort` needs a lawful linear order. PLAN gives `Digest` only `DecidableEq, Hashable, Ord, LawfulBEq`. | Add a bytewise lexicographic `LinearOrder` on `Digest` in `Zrdt/Digest.lean` (proved in `Crdt`) |

Smaller coverage gaps to close cheaply:

- **Output order.** `heads`, the `missing` list and `check`'s "first offending digest" depend on
  HashMap history. The stub-versus-Lean differential test would fail on order alone. Sort every
  output list (`List.mergeSort` has core lemmas; `Array.qsort` has none).
- **Missing theorems:**
  - `accept_digest`: the returned digest equals `hashRecord r`;
  - `has_iff`;
  - `missing` completeness, not just soundness;
  - an `ffi_hash_eq` vector check for the marshalling layer.
- **Dead branches.** With heads recomputed on decode, `CHECK_UNREACHABLE` and the `Tight` half
  only fire on a SHA-256 hash cycle. In production, `check = ok` means every link resolves. Say
  that in the README.

### 1.7 What reload checking actually catches (affects PLAN §3, Beat 4, PLAN_HUMANS §5)

On a decoded blob, `check` reduces to `Closed`. Three changes still pass:

- removing a **head** record (the newest);
- editing a head's payload or author;
- appending a forged record.

This is proved in the model and reproduced. Beat 4 works only if `doctor.ts` removes a record
that **something links**: decode, remove, re-encode. Fix "If the host corrupts the stored blob,
`zrdt_check` on reload catches it, exactly as a tampered server is caught" (PLAN §3, lines 62-63)
and the PLAN_HUMANS trusted-base text.

Also:

- APP §6 has no branch for a **decode** failure.
- 3.3 maps "duplicate digest" to `COLLISION`, but a byte-identical duplicate is not a
  `CollisionIn` (that requires `x ≠ y`).
- 3.4 should say whether decode rejects records that are out of order.

### 1.8 Decode hardening

A hostile or corrupted blob whose u32 count makes the decoder pre-size an allocation hits
`INTERNAL PANIC: out of memory` and `exit(1)`. Under the original plan, stores load at startup
in-process, so Signal would crash on every launch.

- **Rule:** never pre-size from untrusted counts. Bound the count by the remaining input length.
- **Test:** add a fuzz vector.
- With the daemon, the same blob makes the daemon exit, which is fail-closed.

---

## 2. Signal integration

### 2.1 Pin and versions

Pin `v8.33.0` at `be0ed1340b97…` (2026-10-28, latest stable).

- All 39 Signal-side paths APP.md cites exist there, and `packages/mock-server` 27.0.0 is present.
- At the tag, Electron is **44.9.1**, not 45. It has the same Node 24.22.0, N-API 10 and libuv.
  The runtime-spike addons pass on both.
- pnpm is **11.24.0** (`devEngines.packageManager`). `npm i -g pnpm` installs 12.x; it
  auto-switches when online. Use `npm i -g pnpm@11.24.0`.
- Most mock-server line numbers in APP are stale but the functions exist (§3.1).

### 2.2 Send path: wrong hook, and "accept after the send resolves" diverges

`send()` in `ts/messages/send.preload.ts` only awaits a send that has already started.

**The real chain:** `enqueueMessageForSend` (`conversations.preload.ts:4364`) → `NormalMessage`
job → `conversationJobQueue` → `sendNormalMessage` (`ts/jobs/helpers/sendNormalMessage.preload.ts`)
→ `conversation.queueJob` → `sendToGroup` → `getAttrsFromGroupOptions` (a field whitelist that must
be extended) → `Message.toProto` (`SendMessage.preload.ts:381/640`).

**What goes wrong with APP §4's ordering:**

- `send()` catches every error (`send.preload.ts:65-70`), so "after the send resolves" runs on
  every attempt, including a total failure.
- Each attempt re-reads heads. Attempt 2 therefore links attempt 1's own record under the same
  timestamp, and only the recipients still unsent receive it.
- On a partial failure, that produces exactly the false "sent as two versions" marker.

**Freeze-once protocol.** This replaces APP §4's ordering rule. Inside the `queueJob` callback in
`sendNormalMessage`, after attachments are uploaded (their digests are known by then:
`sendNormalMessage.preload.ts:645-703`):

1. If `message.zrdt` exists, send the frozen bytes.
2. Otherwise: read heads, build the Content with links, compute the record from those bytes, and
   `ACCEPT`.
3. Persist `message.zrdt = {links, digest, contentBytes}` first and the store second. Message
   attributes are JSON, so no migration is needed.
4. Send.
5. Never recompute.
6. At startup, re-accept outgoing messages whose digest is missing from the store.

The same per-conversation `PQueue` also runs the incoming `handleDataMessage`
(`handleDataMessage.preload.ts:121`), so a receive cannot slip in between reading heads and
accepting. `handleRetry` already resends stored Content bytes unchanged
(`handleRetry.preload.ts:197-249`).

### 2.3 Receive path: `MessageReceiver` must change

APP §5 says `MessageReceiver` needs "no zrdt logic". That does not hold:

- **Content-level dispatch.** Content-level tags 200/201 throw `Unsupported content message`
  (`MessageReceiver.preload.ts:2667-2671`), even in the fork, unless dispatch is added there.
  Putting the zrdt control messages **inside** the `oneof content` (lines 106-117) matches the
  dispatch. It also avoids adding a new key to roughly 32 `Content` literals, which protopiler's
  `Params` typing would otherwise require.
- **Raw bytes.** The raw plaintext bytes and the authenticated sender are only available together
  there.
- **Early drops.** Several drops happen there before any event exists:
  - bodies over 2 KiB: lines 2114-2119 and 2533-2538;
  - blocked senders: 1606-1614;
  - invalid group data: 2469;
  - storiesBlocked: 2454.

  `handleDataMessage` has more local drops before APP's hook point: blocked, membership,
  announcements-only, terminated, story context, invalid poll, empty. Accepting after those lets
  members' stores diverge.

**Recommendation:** accept after the membership check and before the local-policy drops. Use one
**record predicate** shared by send and receive (§2.4).

**Blocking is a permanent divergence in both directions.** Group sends skip members we blocked
(`SendMessage.preload.ts:1222-1236`). Document it.

### 2.4 What a record is

**Payload.** Do not rebuild it from normalised fields. On receive, the long text is a truncated
2 KiB body plus a long-text pointer at `attachments[0]`. Attachments are split, filtered, capped
at 32 and reordered. The body is whitespace-trimmed
(`handleDataMessage.preload.ts:544-547`), and later replaced by the downloaded long text.

Instead:

```
payload = SHA-256("zrdtP1" ‖ nonce ‖ DataMessage wire bytes with top-level field 200 removed)
```

- **Receive side:** take the bytes from the plaintext in `MessageReceiver` (for sync transcripts,
  `SyncMessage.sent.message`).
- **Send side:** take them from the frozen Content.
- **Re-encoding is safe for Desktop's own messages.** protopiler 4.0.2's decode→encode
  round-trips them byte-identically (checked by running it), so the sync-transcript and
  `handleRetry` re-encodes keep hashes stable. Other clients' bytes must never be re-encoded:
  that matters for the Android stretch.
- **Lean computes it,** so "the host never computes a hash" stays true.
- **It commits to everything the user sees:** quotes, mentions, stickers, previews and polls. The
  three-field payload leaves those uncommitted, which makes content equivocation invisible and
  lets a relay inject fields.

**Wire format.** An empty `repeated bytes zrdt_links = 200` is invisible on the wire, so a fork's
first message (heads = ∅) is byte-identical to a stock message. Use an optional sub-message:

```proto
message ZrdtMeta { repeated bytes links = 1; optional bytes nonce = 2; optional uint32 version = 3; }
optional ZrdtMeta zrdt = 200;   // in DataMessage; present ⇒ record (if in scope)
```

**Scope predicate (v1).** A record is a GroupV2 DataMessage sent by the `NormalMessage` job,
with no `storyContext`, no `reaction` and no `editedMessageTimestamp`. The receiver ignores a
`zrdt` field on anything else.

- **Messages that bypass the hook.** Reactions, poll votes and terminates, deletes (including
  admin deletes), edits, pins and unpins never reach `handleDataMessage`; `onMessageReceived`
  returns earlier.
- **Messages that share the send path.** Reactions, poll votes, stories and edits do go through
  the shared `send()`.
- Without one predicate, the two asymmetries above produce endless gap rows.
- State in PLAN §1 that edits, deletes, reactions, polls and timer/group changes are not covered.
  Stretch: edits and deletes as record kinds.
- 1:1 chats and Note-to-self are out of scope.

**Author.** With author = ACI only, two devices of one account sending from identical heads
satisfy `Equivocation`. That is rare and does not happen in the mock demo. `ACI ‖ deviceId` is
cheap, but optional if the fork marker is redefined (§2.10).

### 2.5 Recovery: today any member can post as Alice. Only the author should resend.

**The attack** (confirmed; nothing in PLAN or APP prevents it):

1. Mallory builds `F = (payload, current heads, author = Alice)`.
2. Mallory sends her own, Signal-authenticated message whose links include `hash(F)`.
3. Every client reports `hash(F)` as missing and requests it.
4. Mallory answers with `F`. Its hash matches.
5. Desktop shows the message as Alice's, because the relayed message must carry
   `sourceServiceId = Alice` for Beat 2 to dedupe correctly. It also counts toward Alice's
   "seen by" and can frame Alice with the fork marker.

An expected-digest check does not close the hole, because Mallory linked the digest herself. Hash
links authenticate content relative to whoever linked it, never relative to the author. This is a
regression against stock Signal, and PLAN_HUMANS's "verified by hash, so it can come from
anyone" claims the opposite.

**Fix: author-only resend through Desktop's existing machinery.**

1. Add `ZrdtResendRequest{groupId, digests}` to the group.
2. Only the member whose own sent message carries that digest answers. They map the digest to
   their own message row, call `getSentProtoByRecipient(requester, sent_at)`, and enqueue the
   existing `SavedProto` job (`handleRetry.preload.ts:236-245`).
3. That job resends the original Content, Signal-authenticated as Alice, only to original
   recipients who are still members, within `RETRY_LIMIT`.
4. The receiver uses the stock path. **Delete `ZrdtResend` and `authorAci`.**
5. The existing trigger cannot be reused as-is. `onRetryRequest` is only reached from
   `decryptionErrorMessage`, which carries `(sentAt, senderDevice)`, not a digest. So a new
   request type plus a digest → own-row lookup is needed.

**What it keeps for free.** sendLog payloads follow Desktop's erase rules: the
`messages_on_delete` trigger, and `deleteSentProtoByMessageId` on delete-for-everyone and
view-once. Lookups prune entries older than 24 h, and delivery receipts prune per recipient. The
victim who never acked keeps their entry, which is exactly the case that matters.

**What it loses:**

- recovery while the author is offline, after 24 h, or from the author's other device;
- routing around a server that targets Alice → Carol specifically.

So the "withheld" verdict must not blame the server (§4). Beat 2 still works: Bob's reply reveals
the gap, and then "Alice's app re-sent it". It also removes the n−1-fold reply amplification of
any-holder answering.

**Desktop does not keep the bytes APP §4 relies on.** "Desktop already stores the sent
`dataMessage` bytes" is wrong. They are in memory only. `_cleanMessageData` strips them before
every DB write, they are cleared after the sync send, and received messages never keep raw bytes.
The sendLog route above is how to get them. `zrdt_get`'s payload would be enough for text-only
beats, but not after §2.8's commitment change.

### 2.6 Persistence: `items` corrupts the blob, and `window.storage` does not exist

- **The blob is corrupted on restart.** `items` values are `JSON.stringify`'d. Only a fixed list
  of keys gets bytes converted to base64. A `Uint8Array` reloads as `{"0":…}` after a restart, so
  Beat 4 and every restart would break. It works within one session only because the in-memory
  copy is still a `Uint8Array`.
- **Every item is loaded into memory** and mirrored into Redux at startup.
- **The API has a different name.** It is `itemStorage` (`Storage.preload.ts:144`), and keys are a
  closed typed union with exhaustiveness assertions (`StorageKeys.std.ts:73`, ~620-655). Dynamic
  `zrdt.store.<conversationId>` keys will not typecheck.

**Use dedicated tables** (a migration in `ts/sql/migrations`, `Server.node.ts`, `Interface.std.ts`):

- `zrdt_records(conversationId, digest, record, PRIMARY KEY(conversationId, digest))`,
  append-only, one row per accept;
- `zrdt_pending(conversationId, digest, record, messageId)`.

Load them lazily per conversation. The pending buffer **must** be persisted. If it is lost, a
message already in the DB has no record, and later messages that link it cause gaps the client
inflicted on itself.

Minimum version for the demo: one base64-string item with debounced writes.

### 2.7 Timeline: "replaced in place" will not happen by default

Desktop orders the timeline by `(received_at, sent_at)`. `received_at` is a local arrival counter
(`incrementMessageCounter`). A recovered message therefore lands **below** Bob's reply.
`retryPlaceholders` cannot help: it is invisible bookkeeping, and it refuses to reposition a
message once the conversation has been opened.

**Fix.** On `MISSING` for message M:

- Restamp M with a new counter.
- Insert a new `zrdt-gap` message type with M's old `received_at` and `sent_at = M.sent_at − 1`.
  This touches the `MessageType` union, `getPropsForMessage`, `isMessageEmpty` and the
  `TimelineItem` switch.
- Save recovered records with the gap's `received_at`.
- Delete the gap row once it resolves.
- Keep the demo machines' clocks in sync, because `sent_at` is the tie-break.

### 2.8 Privacy: the store keeps plaintext that should be gone

- **Problem.** With the PLAN §3.4 payload, every member's append-only store keeps message bodies
  past disappearing timers, delete-for-everyone and view-once. That defeats the device-seizure
  threat model Signal designs for.
- **Problem.** Unsalted digests of low-entropy root records ("ok", "yes") can be brute-forced from
  displayed codes.
- **Fix.** The salted commitment in §2.4 solves both. Content then lives only in Desktop's
  `messages` table and follows its erase paths. With author-only resend, nothing else holds
  content.
- **Still retained.** The DAG metadata (author ACIs, causal shape, count) outlives deleted
  messages. Say so, or disable zrdt in groups with a disappearing timer.

### 2.9 Membership changes are not designed

A member added later starts with an empty store. Under APP §5 the newcomer requests, and is
served, the whole history from before they joined, which Signal deliberately withholds. If
responders refuse, everything the newcomer receives stays pending. Their own messages are roots
with links = ∅, so they also set off the fork marker.

**For this project:**

- Add "membership changes after zrdt genesis" to the non-goals.
- Keep the demo group static.
- Put `groupId` in the request.
- Responders answer only current members who were original recipients. Desktop's retry already
  finds the conversation from the message, not from the request.

**Future work:** an epoch rule in Lean, e.g. accept with `links ⊆ digests s ∪ F`, where F is the
adder's heads carried in the group change.

### 2.10 Fork marker

As defined in APP §7 (equal author, equal links, different digests), it fires on:

- every pair of messages from a stock client or a newcomer (links = ∅);
- multi-device sends;
- retried sends.

A lying author can evade it by perturbing links. Also, Desktop's `(sent_at, sourceServiceId)`
dedupe (`handleDataMessage.preload.ts:124-145`) silently drops the natural same-timestamp second
version, so "both are shown" (PLAN_HUMANS) fails.

**Either drop the fork marker from the demo, or:**

- redefine it on `(author, sent_at)`;
- never silently drop a duplicate whose digest differs;
- exclude records with empty links and relayed records.

### 2.11 Upstream files the patch touches that APP does not list

Assign an owner for the fork's shared root files; PLAN §4's roster has none.

- `protos/SignalService.proto`
- `ts/textsecure/MessageReceiver.preload.ts`
- `ts/jobs/helpers/sendNormalMessage.preload.ts`
- `getAttrsFromGroupOptions`
- the `MessageType` union (`ts/model-types.std.ts:159-182`)
- `StorageKeys.std.ts` (if `items` is used)
- `ts/sql/*` (migration)
- `rolldown.config.ts` and `package.json` (only if N-API is used)
- lint suffix rules

Keep the zrdt code in `ts/zrdt/` with one hook call per path, and organise it for a small diff.

---

## 3. Villain, harness and demo

### 3.1 Hook points and what the server can see

All deliveries to linked desktops go through `Server.handleMessage` (`api/server.ts:733`), then
`Server.send` (`base.ts:1017`). That covers 1:1 websocket sends, gRPC sealed-sender
multi-recipient sends, sync messages, receipts, and queued delivery on reconnect.

**Do not override `send()`** as APP §8a shows. It also intercepts the fake phones' own traffic
(`PrimaryDevice` is built with `send: this.send.bind(this)`), and inside `send()` neither the
source nor the recipient set is visible. **Override `handleMessage`** (for `deviceId ≠ 1`) **plus
`prepareMultiDeviceMessage`**, as the `villain/evil.sketch.ts` spike does.

The sketch is checked against the real API, but has two defects:

- `recipientsByTs` is keyed by timestamp alone, so SKDM fan-outs that share one `Date.now()`
  collide;
- rules must be armed only after a warm-up send.

**The sealed-sender pessimism in PLAN §7 is wrong in the server's favour.** A real server infers
the sender from the multi-recipient recipient set: the group minus the sender. It also infers the
sender from the authenticated `SyncMessage.Sent` to the sender's own account, which carries the
same timestamp within about a second. So "drop Alice's message to Carol" is a legitimate
server-power rule. PLAN Phase E calls the mock "exactly the real server's power", but the mock
process holds every key. That is a policy the rules must follow, not a property of the mock.

### 3.2 Launch harness (`demo/launch.ts` is new work, not a thin reuse)

No existing test puts two or more desktops in one group; only `twoClients` shares a server, and it
is 1:1.

**What the harness must do:**

- `ciMode: 'full'` is **required**. `link()` needs `window.SignalCI`, and with `false` it spins
  in a tight loop. APP §8a's "try `ciMode: false` first" is wrong. The side effects of `'full'`
  are harmless, but they include a 10× shorter retry backoff (`handleRetry.preload.ts:60`), so
  give the zrdt timeouts explicit demo values.
- Every phone is named `'Myself'` (read-only). Patch the fork's bootstrap with a `phoneName`
  option.
- `contactCount: 0`. The defaults are ten "Alice …" contacts.
- Each phone needs the group and the other members in its storage state:
  `StorageState.getEmpty().updateAccount(…).addGroup(group,{whitelisted:true})…`. Note that
  `helpers.createGroup` only writes the creator's state.
- Link the desktops one after another, tile the windows (`BrowserWindow.setBounds`), and do one
  warm-up send per desktop so sender keys are distributed before Beat 1.
- Run it with `node --import tsx demo/launch.ts`.
- **Never relaunch with `bootstrap.startApp()`.** If start fails once, it `fs.rm`s the profile and
  silently relaunches unlinked. Use `await app.close(); await app.start();`, which keeps the
  profile and throws on failure.

**Day-1 spike for lane H3:** desktops exchange sender-key group messages through the mock's gRPC
multi-recipient route. That is the one real unknown. Re-estimate Phase E at 1.5–2 days and about
300–400 lines.

### 3.3 The beats, rewritten so each can happen

The two documents disagree on Beats 3 and 4 today. Rewrite both identically.

- **Beat 1. "Seen by" never fires as scripted.** It needs a *later record* from each member, and
  the beat ends with the checkpoint. Read receipts are on in the mock, so stock "Read" overlaps
  it. Either cut checkpoints, or script "Bob: ok", "Carol: ok" after the checkpoint and label it
  "confirmed by".
- **Beat 2.**
  - Use `dropGroupMsg('alice','carol')` once, matching recipients ≥ 2 and the inferred sender.
    "Next envelope to Carol" can be consumed by a read receipt, a batched delivery receipt or an
    SKDM, and a dropped SKDM is recovered by Signal's own `senderKey.retry`, which would spoil
    the beat.
  - Add a demo-configurable resend delay (3–5 s) so the gap row stays visible.
  - Bob sends a **plain** reply; a quote-reply leaks the dropped text.
  - Narration: "Alice's app re-sent it" (§2.5). Placement needs §2.7.
  - A dropped sender-key or 1:1 message is **not** otherwise recovered by Desktop (verified), so
    the beat is genuinely zrdt's.
- **Beat 3. "Withheld" is unreachable as scripted.**
  - PLAN §8.3's one-shot drop is already spent, so the resend arrives within a second.
  - APP §9's Alice-only filter cannot match the resend.
  - "Queued forever, then villain off" makes Signal, not zrdt, deliver the original.
  - **Rewrite:** `blackhole(carol)` (discard, do not queue). Alice sends; nobody replies. Bob
    clicks **Copy compare code**; Carol pastes it. Carol's app requests the digest, waits for the
    timeout, then shows "Bob has 1 message you don't (·k7f2). Asked; no answer." Clear the
    villain. **Ask again** recovers it.
  - Desktop has **no QR decoder** (only `qrcode-generator`), so drop QR. On one machine the
    clipboard is shared.
  - The compare code moved by copy/paste is the full sorted heads set. Words are only an
    "equal?" fingerprint. 88 bits resists the server, but a malicious member grinding a
    collision needs only about 2^44 work, so use ≥ 12 words (128 bits) if member-resistance is
    claimed.
  - "Withheld" wording must not blame the server (§4).
- **Beat 4.** PLAN §8.4 says "edit on disk and restart". APP says "export/import". The DB is
  SQLCipher; editing it is possible with the key from `config.json`, but impractical. Use APP's
  export/import from **Settings → Internal** (`PreferencesInternal.dom.tsx`, enabled in the mock
  setup). `doctor.ts` must remove a **linked, non-head** record (§1.7). Present the beat as "a
  tampered restore is caught", not as a server attack.
- **"A stock client in the same group" has nothing to run in the mock setup.** The fake phones
  are mock code, and every Bootstrap launches the fork. Either drop the criterion or build a
  separate upstream worktree. If it stays, its link-less messages need a defined treatment (§2.10).
- **The replay rule shows nothing.** Signal discards replays as `DuplicatedMessage`, and then
  dedupes. Keep it as a talking point at most.

---

## 4. Claims and pitch

PLAN §1 says a malicious server "cannot drop, reorder, withhold, or rewrite history without
detection". That contradicts the plan's own `withheld_tail_undetectable` and PLAN_HUMANS §9:

- the tail is invisible until someone replies or compares;
- concurrent messages have no order, and Desktop sorts by arrival;
- "rewrite" was already impossible because of Signal's AEAD.

Suggested replacement:

> A server cannot make a member's app accept a history with a hole in it: if any later message
> builds on one you lack, you are told and it is fetched. Two members can confirm with one code
> that they hold the same set of messages; once the server splits a group it can never merge it
> back without the gap showing. The server can still delay, hold back the newest messages until
> someone replies or members compare, and deliver concurrent messages in different orders.

Also:

- **Gaps are not proof against the server.** A gap or a "withheld" result proves someone is
  inconsistent, not that the server is at fault. A member can link a made-up digest, and an
  offline author produces the same result. Word the UI as "a message Bob has that you haven't
  received", not "the server will not deliver".
- **"Host never decides acceptance" is overstated.** Record selection, payload bytes, resend
  acceptance, the fork marker and compare outcomes are host code. List them in the trusted base.
- **Links are receipts visible to the whole group.** They and "seen by" expose each member's
  receipt state beyond Signal's delivery and read receipts. Say so.
- **Non-goals to add:** membership changes, edits, deletes, reactions, 1:1 chats.

---

## 5. Logistics and environment

### 5.1 This machine cannot run Signal Desktop yet

These need human approval. There is passwordless sudo and Docker; each item takes minutes.

- **Missing system packages.** No Node, nvm, pnpm or xvfb. `libasound.so.2` is missing.
  `libpulse.so.0` is missing too, and ringrtc's Linux addon lists it as NEEDED and is loaded
  eagerly from the main preload. Fix: `sudo apt install libasound2t64 libpulse0 xvfb`.
- **Node and pnpm.** Install Node 24.22.0 persistently (nodejs.org tarball under `~/.local`, or
  nvm), then `npm i -g pnpm@11.24.0`. APP §2's `nvm use` fails here.
- **Disk.** 18 GB free on `/` (down from 20 GB during this review). A Mathlib checkout measured
  6.9 GB, so the plan's main checkout plus four Lean worktrees is about 35 GB before the fork.
  `ubuntu-vg` has 828 GB unallocated: `sudo lvextend -r -L +200G /dev/ubuntu-vg/ubuntu-lv`. Two
  unmounted disks are also attached.
- **Sandbox and display.**
  - AppArmor restricts unprivileged user namespaces, but Playwright 1.60 adds `--no-sandbox` on
    Linux, so the `launch.ts` route needs no setuid helper. Only `pnpm start` does, or
    `ELECTRON_DISABLE_SANDBOX=1`.
  - Electron **does** have a usable headless mode, contrary to APP §1:
    `--ozone-platform=headless --ozone-override-screen-size=1280,800` on the command line (not
    `appendSwitch`) renders real pixels.
- **What was not verified:** Signal itself running under test-mock on this box, which needs
  `pnpm install` and runs Signal's scripts. Decide the demo laptop's OS on day 1, and do the
  first full fork build there.

### 5.2 Smaller corrections

- **`NODE_APP_INSTANCE`** only selects `config/local-<name>.json`, which must set
  `storageProfile`. On the mock route, `storagePath` in `SIGNAL_CI_CONFIG` decides anyway.
- **`SIGNAL_ENABLE_HTTP`** is not a TLS escape hatch for §8b: it never touches `serverUrl`, the
  HTTPS agent or libsignal-net. Drop it from the stretch plan.
- **Electron 44/45 download their binary lazily** on first `require`. Use `install-electron`.
- **APP §2's production comment** contradicts CONTRIBUTING and is hazardous.
- **Signal's public CI does not run test-mock.** The job is gated on `Signal-Desktop-Private`. A
  public fork gets no mock CI unless that condition is edited, so the gates below run locally.
- **Don't vendor the binaries in git.** Vendoring `libzrdt.a` plus the Lean runtime archives into
  the fork would bloat it; this is moot with `zrdtd` (point to it by path).
- **Phase C estimate.** 1–2 days is unrealistic for N-API (3–4 days). With `zrdtd` it is about
  1–1.5 days.

### 5.3 A fallback gate that can actually be operated

PLAN §7 and APP §10 have no date and no test. Replace them with these dated checkpoints:

- **F0, end of day 1, on the Mac mini.** `pnpm install` and `pnpm run generate` succeed at
  `v8.33.0`, and `pnpm start` shows the link screen. Also
  `pnpm exec mocha ts/test-mock/messaging/twoClients_test.node.ts` passes (no xvfb on macOS),
  the backend shows its kind and version on screen, and `zrdtd`, built natively on the Mac,
  completes one `ACCEPT` round trip inside the fork's Electron (§1.3).
- **F1, day 2.** `launch.ts` brings up three desktops in "Camping". Stock messages flow, and
  `dropGroupMsg` visibly drops one envelope.
- **F2, day 3: go/no-go.** An automated `demo/smoke.ts` (Playwright) runs: Alice sends three
  messages, and Bob and Carol report `accepted` with the same digests. With the drop rule armed,
  Carol reports `MISSING` naming the dropped digest. If this is not green, start the mini-client
  on day 4 with a 2-day budget.
- **F3, day 5.** The author-resend round trip and the gap and code UI work.
- **F4, day 6.** The backend is switched to the Lean daemon, and there is a cold-start rehearsal.

**For the fallback to really reuse work:**

- Write the rules as pure `demo/rules.ts` with two adapters: `EvilServer`, and a roughly 100-line
  ws relay.
- Keep the zrdt UI in `ts/zrdt/ui` with plain props and strings, its own CSS, and no imports from
  Signal's `ts/`.

---

## 6. Checked and correct (keep)

- **Wire basics.**
  - `SignalService.proto` is proto2. DataMessage uses tags 1–29, so 200 is free and legal.
  - protopiler 4.0.2 keeps unknown fields in `$unknown` and re-emits them.
  - Stock Desktop, Android, iOS and the mock phones drop an unknown Content without UI or retry.
    Desktop logs it at error level, so APP §3's "ignores them entirely" should say "logs and
    drops".
- **Authenticated timestamp.** `DataMessage.timestamp` must equal the envelope timestamp
  (`processDataMessage.preload.ts:654-666`), so the payload timestamp is Signal-authenticated.
- **Attachment digests.** `AttachmentPointer.digest` is field 6, 32 bytes, and is known before the
  proto is built.
- **Sync transcripts** carry the DataMessage, including unknown fields, to the user's other
  devices.
- **Per-conversation serialisation exists:** a PQueue with concurrency 1 per conversation, with
  the attempt loop inside the slot.
- **Native modules can load in the main-window preload.** It runs `sandbox:false`, with
  `contextIsolation` in the mock (non-test) environment; libsignal-client and ringrtc already
  load there.
- **Electron and Node.** Electron 45/44 embed Node 24.22.0 = `.nvmrc`. An addon built against
  Node headers loads in Electron without a rebuild.
- **The plan's Lean init sequence works:** `lean_initialize_runtime_module` → `initialize_<pkg>_<Mod>(1)` →
  `lean_io_mark_end_initialization`, in 2–3.5 ms. Initialisers are idempotent.
- **Handle API performance.** A HashMap store with the shim holding the only reference does
  O(1) in-place accepts, 1.3–2.4 µs flat up to 64k records. No leak was seen over 8M calls.
- **No OpenSSL clash.** The runtime plus Init/Std needs no OpenSSL, and Electron's BoringSSL
  exports no `SSL_`/`EVP_` symbols.
- **Encoding.** The record encoding is prefix-free and injective within the size bounds. Sorted,
  deduplicated links are the right canonical form for `Finset`.
- **The COLLISION status** and its `abs_accept` clause have the right shape.
- **Mock server.**
  - Several Bootstraps can share one server, each with its own fake primary and profile.
  - Groups v2 with zkgroup works end to end.
  - `SIGNAL_CI_CONFIG` injection works as APP describes.
  - Typing indicators are off.
  - `desktop.senderKey.retry` only fires on decryption errors, so drops are not silently healed.
- **Beat 4 hook.** Settings → Internal exists and is enabled in the mock setup.
- **Staying on v4.35.0** (PLAN §9 Q5): nothing in the build pipeline argues for a bump. Note that
  4.35 package-prefixes exported symbols (`initialize_<pkg>_…`), so renaming the Lake package
  renames every init symbol.

---

## 7. Decisions for you

| # | Decision | Recommendation |
|---|---|---|
| 1 | In-process N-API vs `zrdtd` daemon | `zrdtd`, with one Lean dispatcher; N-API as a macOS stretch |
| 2 | SHA-256 (PLAN §9 Q4) | Pure Lean |
| 3 | Theorem restatements (§1.1, §1.6) | Approve: `Rec`/`toSpec`, `Equiv` form of `decode_encode`, `WellSized`, `Closed ∈ Inv`, `LinearOrder Digest` |
| 4 | Recovery model | Author-only resend via sendLog; delete `ZrdtResend` |
| 5 | Payload | Salted commitment over wire bytes minus field 200, computed in Lean |
| 6 | Scope | GroupV2 normal messages only; static membership; 1:1 out |
| 7 | Fork marker and checkpoints | Cut from the demo unless redefined (§2.10, §3.3) |
| 8 | Pitch | Adopt the §4 wording |
| 9 | Environment | **Decided:** the fork is built and run on the Mac mini (§0a). Still open: SSH access from this box or Claude Code on the Mac, and whether the Mac mini is the demo machine. The Linux LV extend is still needed for the Lean worktrees. |
| 10 | Deadline (PLAN §9 Q1) | Needed to date F0–F4 |

---

## Appendix: evidence and artifacts

- **Full reviewer output** (findings with file:line evidence, commands and output excerpts) and
  the verifier verdicts are in this session's workflow transcripts:
  - `~/.claude/projects/-home-kejace-devel-zrdt/546e781c-…/subagents/workflows/wf_cc64d905-468/journal.jsonl` (review)
  - `…/wf_2753fa62-2e6/journal.jsonl` (verification)
- **Spike directories** are under `/tmp/zrdt-spike-*` and `/tmp/zrdt-verify-*` (about 2.3 GB;
  volatile).
- **Kept sources**, kept outside the repo (`~/devel/zrdt-review-spikes` on the reviewer's machine):
  - `pure-lean-core/`: Mathlib-free `Sha256.lean` (NIST-checked), `Digest.lean`, `Store.lean`,
    `Ffi.lean`, and a `lakefile.toml` showing the `:static` facet and the TOML extern workarounds.
  - `one-dispatcher/`: `Zv.lean` (one `handle`, served over stdin/stdout and as an `@[export]`)
    and `host.c`. **Note the short-read bug in its loop** (§1.3).
  - `villain/evil.sketch.ts`: EvilServer overriding `handleMessage` and
    `prepareMultiDeviceMessage`. Untested; see the defects in §3.1.
  - `pic-runtime/build_rt_pic.sh`: option B runtime rebuild.
  - `c-header/zrdt.h`: corrected C header sketch, only relevant if in-process N-API is kept.
