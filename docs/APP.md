# APP.md: integrating zrdt into Signal Desktop for the demo

Status date: 2026-11-01. Audience: whoever forks Signal Desktop, writes the villain (mock server or
proxy), and runs the demo. Companion documents: `PLAN.md` (phases, gates, who does what),
`PLAN_HUMANS.md` (the theorems) and `RESTORE_PLAN.md` (history import from any peer, confirmed by
live messages). This file is only about getting zrdt into a Signal client and on screen.

Review of 2026-11-01: `docs/review-2026-11-01/` (`REVIEW.md`, `UPDATE-690ae65.md`,
`AMENDMENTS.md`). `AMENDMENTS.md` is the source of names and decisions; each change it made here is
marked **[amendment]**.

Facts below marked **(verified)** were checked against `signalapp/Signal-Desktop`: first on `main`
on 2026-10-31, then by the review against `main` @5dad34ad and the `v8.33.0` tag, where every
Signal path the earlier version of this file cited exists (review §2.1). Line numbers come from the
review; confirm them at the pin. Anything marked **confirm on checkout** is a best guess from file
names and must be checked in the editor before relying on it. The fork starts from `v8.33.0` (§1).
**[amendment]**

## 0. The one-paragraph plan

**[amendment]** Fork Signal Desktop at `v8.33.0`, and build and run it on the Mac mini. Add one
optional sub-message, `ZrdtMeta zrdt = 200`, to `DataMessage`, so every in-scope group message
carries the sender's heads (its links), a 32-byte nonce, and a list of records the sender disowns.
All zrdt logic runs in `zrdtd`, a small Lean program beside Signal. It holds one `CheckedStore`
per chat, so every store it holds is checked by its type, and it answers framed requests on
stdin/stdout. On send and on receive, the fork asks `zrdtd` for the message's commitment (a salted
SHA-256 over the message's wire bytes) and then to accept the record; the fork itself never hashes.
What the fork still decides (which messages are records, which bytes it passes, provenance, UI
wording) is in the trusted base. Desktop keeps the records in SQL tables, keeps the message content
(the "opening") as an erasable message attribute, and re-opens each store from its rows at
startup. The host marks each record `live`, `relayed` or `imported`; `zrdtd` turns that into what
the user sees (confirmed by its author, held by a member, unconfirmed, not confirmed by its
author). Add a few small UI pieces (code, gap row, compare by copy and paste, rejected banner,
provenance labels, import/export). Run four desktops against a Signal server we control and make
it misbehave on cue. Signal keeps doing confidentiality and sender authentication; zrdt shows
members when their histories have a hole or differ.

## 1. Target and rationale

**Primary: Signal Desktop fork, pinned at `v8.33.0`** (`be0ed1340b9798323d59129b43504062d235e23d`,
2026-10-28, the latest stable tag). TypeScript, React 19, Electron **44.9.1** at that tag
(Electron 45 is only on `main`), Node 24.22.0, `packages/mock-server` 27.0.0 (review §2.1). Fast UI
iteration; server URL and trust roots are plain config; the main process can easily spawn a
helper process. **[amendment]**

**Where it runs: the Mac mini** (darwin-arm64). The fork is built and run there. `zrdtd` is built
there too, with the darwin Lean toolchain; nothing can be cross-built. The Linux box keeps the Lean
proof work (Mathlib, the gate, Comparator). **[amendment]**

**Stretch: Signal Android fork.** Phones are more compelling on stage, but NDK/JNI, long builds,
and emulator proxying cost days. Section 11.

**Accounts.** A Signal Desktop normally links to a phone. Two ways around needing four phones
**[amendment: four members, for beat 5]**:

- **Mock server (recommended, section 8a).** The Desktop repo ships `packages/mock-server`
  (`@signalapp/mock-server` 27.0.0), a mock Signal server used by the `ts/test-mock` Playwright
  suite **(verified)**. Its `Bootstrap` class creates a fake primary device ("phone"), links a
  desktop to it, and several bootstraps can share one server (`new Bootstrap({ server:
  bootstrap1.server })`, as `ts/test-mock/messaging/twoClients_test.node.ts` does) **(verified)**.
  No phone numbers, no SMS, no rate limits, and we own delivery.
- **Staging (fallback for "it's the real Signal network").** Dev builds connect to
  `chat.staging.signal.org` by default (`config/default.json`) **(verified)**. `CONTRIBUTING.md`
  describes registering a dev desktop as a *standalone* device on staging with a phone number
  (Relink → Standalone → verify) **(verified)**; four numbers are needed, SMS/captcha applies.

**Several desktops on one machine.** **[amendment]** `NODE_APP_INSTANCE=alice pnpm start` only
selects `config/local-alice.json`; that file must set `storageProfile` to get a separate data
directory (review §5.2). The mock-server path launches each instance with its own temp profile via
Playwright's `_electron.launch` **(verified, `ts/test-mock/playwright.node.ts`)**; there,
`storagePath` in `SIGNAL_CI_CONFIG` decides. The demo uses visible windows. Electron does have a
headless mode for unattended runs: `--ozone-platform=headless --ozone-override-screen-size=1280,800`
on the command line (not `appendSwitch`) renders real pixels (checked on Linux, review §5.1). One
machine runs all four desktops.

## 2. Build

**[amendment]** Toolchain on the Mac: Xcode Command Line Tools, Python 3, Node `24.22.0`
(`.nvmrc`), pnpm `11.24.0` (`devEngines.packageManager`). A plain `npm i -g pnpm` installs 12.x, so
pin the version.

```sh
xcode-select --install                     # once: Xcode Command Line Tools
git clone git@github.com:<org>/Signal-Desktop.git && cd Signal-Desktop   # the fork, branched from v8.33.0
nvm use                                    # Node 24.22.0 from .nvmrc
npm i -g pnpm@11.24.0
pnpm install        # builds native deps; postinstall runs electron:install-app-deps
pnpm run generate   # protos, JS, CSS (generate:phase-0, generate:phase-1)
pnpm start          # staging by default; never point a dev build at production with a phone that matters (CONTRIBUTING, "Changing to production")
```

**[amendment]** The `pnpm start` comment no longer names a production config file; the old one was
wrong and invited a production connection (review §5.2).

**[amendment]** The Electron binary downloads lazily on first use, so the first launch needs the
network. Fetch it before the demo (review §5.2 names `install-electron`; confirm on checkout).

**Launch Signal from the Mac's GUI session** (Terminal or Screen Sharing), not from a plain SSH
session. Electron windows need the Aqua session, and Desktop's DB key goes through `safeStorage`,
which uses the login Keychain; that is normally locked over SSH. Check on day 1 whether the mock
launch touches the Keychain. Agents reach the Mac either through the Linux dev box's SSH key
(add it on the Mac) or by running Claude Code on the Mac. **[amendment]**

Dev loop: `pnpm run dev:transpile` and `pnpm run dev:styles` watch; restart the app to pick up
changes **(verified, CONTRIBUTING)**. Packaging: `pnpm run build` → `electron-builder`
26.11.1 **(verified)**; `SKIP_SIGNING_SCRIPT=1 pnpm run build` for unsigned local builds.

**The zrdt backend: `zrdtd`.** **[amendment]** zrdt runs in a separate process, `zrdtd`, not
inside Signal. It is a `lean_exe` in this repo's `core/` package (`zrdt-core`), which has no
Mathlib, so the Mac builds it with only the Lean toolchain:

```sh
cd zrdt/core && lake build zrdtd                  # on the Mac, darwin-arm64
export ZRDT_DAEMON=$PWD/.lake/build/bin/zrdtd     # the fork finds it by path; no binary goes into git
```

`zrdtd` reads frames `u32 BE length ‖ u8 op ‖ body` on stdin and answers on stdout in request
order; diagnostics go to stderr. It runs with `LEAN_ABORT_ON_PANIC=1`, so a Lean `panic!` stops it
instead of returning a default value. The ops (`VERSION`, `NEW`, `OPEN`, `SALVAGE`, `COMMIT`,
`HASH`, `ACCEPT`, `HEADS`, `HAS`, `GET`, `REACH_SET`, `MERGE`, `CLASSIFY`, `ENCODE`, `CLOSE`) and
their replies are the contract in `PLAN.md` §3.3. All digest lists in replies are sorted.

Files in the fork **[amendment]**:

```
ts/zrdt/
  ZrdtBackend.std.ts         async interface, one method per frame op
  backends/daemon.node.ts    spawns $ZRDT_DAEMON with LEAN_ABORT_ON_PANIC=1; frames on stdin/stdout
  backends/stub.node.ts      day-1 TypeScript stub, same interface
  ui/                        zrdt components: plain props, own CSS, no imports from Signal's ts/
demo/
  evil.ts rules.ts launch.ts doctor.ts smoke.ts     villain and harness (§8a, §9, §10)
```

```ts
// ts/zrdt/ZrdtBackend.std.ts: a sketch; the frame ops in PLAN.md §3.3 are the contract
type Bytes = Uint8Array;
type Digest = Bytes;                                   // 32 bytes
type ChatKey = string;                                 // the conversation id
type Parts = { group: Bytes; commit: Bytes; links: Array<Digest>; author: Bytes };
type Refused = { kind: 'malformed' | 'tooLarge' | 'wrongChat' } | { kind: 'collision'; digest: Digest };
type Opened = { kind: 'ok' } | Refused | { kind: 'unverifiable'; unverifiable: Array<Digest>; missing: Array<Digest> };
type Salvaged = { kind: 'ok'; dropped: Array<Digest>; missing: Array<Digest> } | Refused;
type Accepted = { kind: 'accepted'; digest: Digest; record: Bytes }   // protocol 2: the record's bytes
  | { kind: 'missing'; digests: Array<Digest> }
  | { kind: 'collision'; digest: Digest } | { kind: 'wrongChat' } | { kind: 'tooLarge' };
type AcceptedRecord = Accepted | { kind: 'malformed' } | { kind: 'badOpening' };      // ACCEPT_RECORD
type Provenance = { kind: 'live' } | { kind: 'relayed'; by: Bytes } | { kind: 'imported' };
type Status = { kind: 'confirmedByAuthor' } | { kind: 'heldBy'; aci: Bytes }   // one ACI: the smallest holder
  | { kind: 'unconfirmed' } | { kind: 'notConfirmedByAuthor' };

export interface ZrdtBackend {
  readonly kind: 'lean' | 'stub';                                              // shown on screen
  version(): Promise<{ protocol: number; build: string }>;                     // VERSION
  create(chat: ChatKey, group: Bytes): Promise<void>;                          // NEW
  open(chat: ChatKey, group: Bytes, input: Bytes | Array<Bytes>): Promise<Opened>;       // OPEN
  salvage(chat: ChatKey, group: Bytes, input: Bytes | Array<Bytes>): Promise<Salvaged>;  // SALVAGE
  commit(group: Bytes, author: Bytes, nonce: Bytes, dataMessage: Bytes)
    : Promise<{ commit: Digest; opening: Bytes }>;                              // COMMIT (protocol 2)
  hash(r: Parts): Promise<Digest>;                                             // HASH
  accept(chat: ChatKey, r: Parts): Promise<Accepted>;                          // ACCEPT
  acceptRecord(chat: ChatKey, record: Bytes, opening?: Bytes): Promise<AcceptedRecord>; // ACCEPT_RECORD
  heads(chat: ChatKey): Promise<Array<Digest>>;                                // HEADS
  has(chat: ChatKey, d: Digest): Promise<boolean>;                             // HAS
  get(chat: ChatKey, d: Digest): Promise<Parts | undefined>;                   // GET
  reachSet(chat: ChatKey, from: Array<Digest>): Promise<Array<Digest>>;        // REACH_SET
  merge(chat: ChatKey, blob: Bytes): Promise<Opened>;                          // MERGE
  classify(chat: ChatKey, facts: Array<{ digest: Digest; provenance: Provenance; disown: Array<Digest> }>):
    Promise<Array<{ digest: Digest; status: Status }>>;                        // CLASSIFY
  encode(chat: ChatKey): Promise<Bytes>;                                       // ENCODE
  close(chat: ChatKey): Promise<void>;                                         // CLOSE
}
```

- **Where it is spawned.** From the main process, serving the window through `ipcMain.handle` (as
  `app/sql_channel.main.ts` does for SQL), which survives renderer reloads. Or from the
  main-window preload, which runs with `sandbox:false` (`app/main.main.ts:725-728`) and so can use
  `node:child_process`. Every call site is already async (the send job, `conversation.queueJob`,
  SQL over IPC), so an async backend costs nothing (review §1.3). Both ends must read until a
  whole frame has arrived: a read can return fewer bytes than asked.
- **Fail closed.** If `zrdtd` exits, show a "zrdt unavailable" banner and mark nothing accepted. On
  restart, re-`OPEN` every open chat from its SQL rows (§6). `ZRDT_REQUIRE_LEAN=1` refuses the
  stub. The backend's kind and version are always shown on screen.
- **Day-1 stub.** `stub.node.ts` implements the same interface in plain TypeScript, so the
  integration and UI can be built before the Lean side lands. It is also the independent
  reimplementation for the differential test: rung 7 runs `vectors.json` through the stub and
  through `zrdtd` on the Mac and compares the results. Swapping in `zrdtd` must not change any
  other TypeScript.
- **Optional stretch, macOS only:** an in-process `.node` over the same Lean `handle`, exported as
  `zrdt_l_call`. About 20 lines of C. It copies every output (Electron rejects external buffers),
  guards every entry with an initialised flag, and throws if it fails to load, never falling back
  to a no-op. The shipped Linux Lean runtime cannot be linked into a `.node`; macOS is very likely
  fine. Time box: 2 hours on day 1 (review §0a, §1.4).

**Day-1 checks on the Mac** (checkpoint F0 in `PLAN.md`). **[amendment]**
- `pnpm install` and `pnpm run generate` succeed at `v8.33.0`, and `pnpm start` shows the link
  screen;
- `pnpm exec mocha ts/test-mock/messaging/twoClients_test.node.ts` passes;
- the backend shows its kind and version;
- `zrdtd` completes one `ACCEPT` round trip inside the fork's Electron;
- `kill -9` on `zrdtd` shows the banner.

Signal's public CI does not run test-mock (the job is gated on the private repository), so these
checks and the gates run locally.

## 3. Message mapping and wire format

**[amendment]** A zrdt record is `(group, commit, links, author)`, encoded as
`"zrdt2" ‖ group(32) ‖ commit(32) ‖ u32 nlinks ‖ links ‖ author(16)` (`PLAN.md` §3.4):

- `group` = the group's 32-byte id. The group id inside the hash binds a record to its chat, so a
  resend or import from another group is rejected (`WRONG_CHAT`).
- `commit` = `SHA-256("zrdtP1" ‖ group ‖ author ‖ nonce(32) ‖ DataMessage wire bytes with
  top-level fields 15 and 200 removed)`. Field 15 is `groupV2`, which contains the group master
  key; field 200 is `zrdt` itself. `zrdtd` computes it (`COMMIT`); the TypeScript never hashes and
  never concatenates bytes. It covers the timestamp and everything the user sees: body, quote,
  mentions, attachments, previews, stickers. The timestamp is Signal-authenticated:
  `DataMessage.timestamp` must equal the envelope timestamp (`processDataMessage.preload.ts:654-666`)
  **(verified)**.
- `nonce` = 32 random bytes per message, sent in `ZrdtMeta.nonce`. Without it, a short message
  ("ok") could be guessed from its code.
- `links` = the sender's heads at send time (`HEADS`), strictly sorted, no duplicates.
- `author` = sender ACI, 16 bytes (the ACI is what sealed sender authenticates).

**Why the wire bytes, not rebuilt fields.** **[amendment]** On receive, Desktop truncates long text
to a 2 KiB body plus a long-text attachment, trims whitespace, and splits, filters, caps and
reorders attachments (review §2.4). Rebuilding identical bytes on both sides is fragile; hashing the
bytes as sent is not. The bytes come from:
- the send side: the frozen Content built in §4;
- the receive side: the decrypted plaintext in `MessageReceiver` (for sync transcripts,
  `SyncMessage.sent.message`).

Desktop's own messages survive protopiler 4.0.2's decode → encode byte for byte, so sync
transcripts and `handleRetry` re-sends keep their hashes. Other clients' bytes must never be
re-encoded.

**The opening** is `nonce ‖ the committed bytes`: the DataMessage with top-level fields 15 and 200
already removed. It is the message content. It is not in the store; Desktop keeps it as an
erasable message attribute (§6). Because field 15 is never in an opening, no stored attribute,
relay or dump carries the group master key. When an opening is re-entered into Desktop, the host
supplies the group context from the conversation itself. **[amendment]** With protocol 2,
`COMMIT` returns the opening together with the commitment, so the host never strips fields or
concatenates bytes itself. **[amendment]**

The digest (`ACCEPT`'s reply; SHA-256 over the record encoding) is **never sent**. Each receiver
recomputes it. If the sender and receiver hash different bytes, the message simply fails to link
for others; that is a bug to catch with the differential tests in `PLAN.md`, not a security event.

**What is a record: the scope predicate.** **[amendment]** One predicate, shared by send and
receive: a GroupV2 `DataMessage` from the `NormalMessage` send job, with no `storyContext`, no
`reaction` and no `editedMessageTimestamp`. The receiver ignores a `zrdt` field on anything else.
- Not covered: edits, deletes, reactions, polls, pins, timer, profile and group changes.
- 1:1 chats and Note-to-self are out.
- Membership changes after zrdt genesis are a non-goal. The demo group is static: Dave is a member
  from creation.

Without one shared predicate, messages that take different paths on send and receive produce
endless gap rows (review §2.4).

**Proto change** (`protos/SignalService.proto`, proto2; `DataMessage` uses tags 1–29 today, so 200
is free **(verified)**): **[amendment]**

```proto
message ZrdtMeta {
  repeated bytes links   = 1;   // 32-byte digests: the sender's heads at send time
  optional bytes nonce   = 2;   // 32 bytes, the commitment salt
  optional uint32 version = 3;
  repeated bytes disown  = 4;   // digests of records in the sender's name it did not create (§5)
}
message DataMessage { ... optional ZrdtMeta zrdt = 200; }   // present ⇒ record, if in scope

message ZrdtResendRequest { bytes groupId = 1; repeated bytes digests = 2; }
message ZrdtResend        { bytes groupId = 1; bytes record = 2; optional bytes opening = 3; } // opening = nonce ‖ DataMessage bytes without fields 15 and 200
message ZrdtNotFound      { bytes groupId = 1; repeated bytes digests = 2; }
message Content { oneof content { ...; ZrdtResendRequest zrdtResendRequest = 200;
                                       ZrdtResend zrdtResend = 201; ZrdtNotFound zrdtNotFound = 202; } }
```

- **Why a sub-message:** an optional sub-message is on the wire even when it is empty. An empty
  `repeated bytes` field is not, so a fork's first message (no heads yet) would look exactly like
  a stock one. **[amendment]**
- **Why inside the `oneof`:** it matches `MessageReceiver`'s dispatch, and avoids adding a new key
  to about 32 `Content` literals. **[amendment]**
- Links go in `DataMessage`, so they are inside the same sender-key or pairwise ciphertext as the
  body. The three control messages go at `Content` level, next to `DecryptionErrorMessage`.
- **Stock clients.** **[amendment]** Stock Desktop keeps the unknown `DataMessage` field in
  `$unknown` and ignores it; `isUnsupportedMessage` keys on `requiredProtocolVersion`, not on
  unknown tags **(verified, `ts/messages/handleDataMessage.preload.ts`)**. An unknown `Content`
  message is logged as "Unsupported content message" at error level and dropped; nothing is
  rendered (Desktop, Android, iOS and the mock phones; review §6).

**[amendment]** `ZrdtResend` carries the record and, if the responder still holds it, its opening.
The record bytes are the ones `ACCEPT` returned (protocol 2), so the responder never re-encodes a
record. The receiver passes both to `ACCEPT_RECORD` (`0x10`): `zrdtd` replies `MALFORMED` if the
bytes are not exactly a record's encoding, `BAD_OPENING` if the opening's commitment (under the
record's group and author) is not the record's commit or the opening holds field 15 or 200, and
otherwise accepts the record as `ACCEPT` does. The returned digest names the gap it fills. Signal authenticates the responder, not the author, and the hash only proves this is
the record someone linked. So a relayed message is shown as "relayed by X" until its author confirms it (§5, §7).

Protos are compiled by `pnpm run generate` into `ts/protobuf/` **(verified placeholder dir)**;
confirm the exact `generate:phase-0` script in `package.json` on checkout.

## 4. Send path

**[amendment]** The real chain (review §2.2): `enqueueMessageForSend`
(`ts/models/conversations.preload.ts:4364`) → `NormalMessage` job → `conversationJobQueue` →
`sendNormalMessage` (`ts/jobs/helpers/sendNormalMessage.preload.ts`) → `conversation.queueJob` →
`sendToGroup` → `getAttrsFromGroupOptions` → `Message.toProto`
(`ts/textsecure/SendMessage.preload.ts:381/640`).

**The hook** **[amendment]** is inside the `conversation.queueJob` callback in `sendNormalMessage`,
after attachments are uploaded (`sendNormalMessage.preload.ts:645-703`; their digests are known by
then). **Freeze once:**

1. If `message.zrdt` already exists (a retry), send its frozen bytes and stop.
2. links = `HEADS`.
3. Generate a 32-byte nonce.
4. Build the Content bytes with `ZrdtMeta{links, nonce, version, disown}`. `disown` lists records
   in our own name that we did not create (§5).
5. `COMMIT` over the DataMessage bytes, then `ACCEPT` the record. It must return `accepted`: our
   own links always resolve.
6. Persist `message.zrdt = {links, nonce, digest, contentBytes}` first and the store row second.
   Message attributes are JSON, so this part needs no migration.
7. Send the frozen bytes, on this attempt and every later one. Never recompute.
8. At startup, re-accept outgoing messages whose digest is missing from the store.

Extend `getAttrsFromGroupOptions` (a field whitelist) so the frozen `zrdt` field reaches
`Message.toProto`. **[amendment]**

**Not `ts/messages/send.preload.ts`.** **[amendment]** `send()` only awaits a send that has already
started. It catches every error (`send.preload.ts:65-70`), so "after the send resolves" also runs
after a total failure. A second attempt would also re-read the heads and link the first attempt's
own record under the same timestamp (review §2.2).

**Desktop does not keep sent `DataMessage` bytes.** **[amendment]** `_cleanMessageData` strips them
before every DB write, and they are cleared after the sync send (review §2.5). The frozen
`contentBytes` and the `zrdtOpening` attribute (§6) are zrdt's own copies.

`contentBytes` is plaintext too, so `message.zrdt` is classified `erase` in
`messageAttributesEraseBehavior`, like `zrdtOpening`. The table is exhaustive, so the fork must
classify `zrdt` anyway. Desktop's delete, expiry and view-once paths then remove it. The digest and
links are structure and stay in `zrdt_records`. **[amendment]**

- `ts/util/sendToGroup.preload.ts` (`sendToGroup`, `sendContentMessageToGroup`,
  `sendToGroupViaSenderKey`) **(verified)**: no change; `ZrdtMeta` rides inside the content.
- Own-device sync messages (`sendSyncMessage` in `send.preload.ts`) carry the same DataMessage
  bytes, unknown fields included **(verified)**, so a linked phone or second desktop gets the links
  for free.

Ordering rule: compute heads and accept **inside the per-conversation send queue** (a `PQueue` with
concurrency 1), so two rapid sends from one client link each other instead of both linking the same
old heads.

## 5. Receive path

Touchpoints **(paths verified; line numbers from the review)**: **[amendment]**

- `ts/textsecure/MessageReceiver.preload.ts`: **the hook.** Only here are the raw plaintext bytes
  and the authenticated sender available together.
  - Add dispatch for `Content` 200–202. Without it they throw "Unsupported content message"
    (`:2667-2671`), even in the fork.
  - Accept **after the membership check and before the local-policy drops**, so that members'
    stores do not diverge over local settings. Drops that happen here, before any event exists:
    bodies over 2 KiB (`:2114-2119`, `:2533-2538`), blocked senders (`:1606-1614`), invalid group
    data (`:2469`), `storiesBlocked` (`:2454`). `handleDataMessage` drops more later: blocked,
    announcements-only, terminated, story context, invalid poll, empty.
- `ts/textsecure/processDataMessage.preload.ts`: normalises proto → internal shape. Carry `zrdt`
  (links, nonce, disown) along.
- `ts/background.preload.ts` (`onMessageReceived`; the `decryption-error` and `retry-request`
  listeners) **(verified)**: add handlers for the three zrdt `Content` messages beside the
  retry-request handler.
- `ts/messages/handleDataMessage.preload.ts` (`handleDataMessage`) **(verified)**: no accept here.
  It is the **only** place a relayed message re-enters Desktop, through the scope predicate; never
  through `onMessageReceived`'s delete, pin or poll branches.

**Provenance per record** (host state, trusted; table `zrdt_provenance`, §6): **[amendment]**
- `live`: the Signal envelope sender equals the record's author, or this device sent it;
- `relayed(byAci)`: the record came in a `ZrdtResend` from another member;
- `imported`: from a dump, or kept by "Keep what verifies".

**Per incoming in-scope group message, in `MessageReceiver`:** **[amendment]**

1. `COMMIT(group, sender ACI, ZrdtMeta.nonce, DataMessage bytes)` returns the commitment and
   the opening; then `ACCEPT(chat, {group, commit, links, author = sender ACI})`. The record is
   `live`. **[amendment]** (protocol 2)
2. `ACCEPTED{digest, record bytes}`: write the `zrdt_records` row with those bytes; set
   `zrdtDigest`, and `zrdtOpening` to the opening `COMMIT` returned, on the message (§6); record the message's `disown` digests in `zrdt_provenance`; drain the pending
   buffer (retry every pending record whose links are now present); re-run `CLASSIFY`.
3. `MISSING{digests}`: write the record to `zrdt_pending` and insert a `zrdt-gap` row above the
   message (§6). After `ZRDT_RESEND_DELAY_MS` (3–5 s in the demo), send
   `ZrdtResendRequest{groupId, digests}` 1:1 to the member whose message referenced them. An
   answer can be a `ZrdtResend`, a `ZrdtNotFound`, or, if that member is the author, the original
   re-sent through the sendLog (step 6). If `ZrdtNotFound` arrives for some digests, or digests
   are still missing after the timeout, send the request for the still-missing digests to the
   group. **[amendment]** Reuse the dedupe and backoff of `ts/util/handleRetry.preload.ts`
   **(verified)**: one request per digest per minute. `ciMode: 'full'` makes its retry unit 10×
   shorter (`handleRetry.preload.ts:60`), so give the zrdt timeouts explicit values.
4. `COLLISION{digest}`: a different record with the same digest is already in the store. Do not
   store it as a normal message; show it with the digest. With SHA-256 this never fires in
   practice; it exists so the code matches the model's collision clause at the one place it is
   observable.
5. `WRONG_CHAT` or `TOO_LARGE`: drop and log. `WRONG_CHAT` means the record came from another
   group via a resend or an import; `TOO_LARGE` means it breaks the size limits in `PLAN.md` §3.4.

**Answering and receiving resends:** **[amendment]**

6. **On `ZrdtResendRequest`** from a current member, for each digest we hold (`GET`):
   - if it is our own message and the sendLog still has it, re-send the original through Desktop's
     sendLog/`SavedProto` path: map the digest to our message row, call
     `getSentProtoByRecipient(requester, sent_at)`, and enqueue the existing `SavedProto` job
     (`handleRetry.preload.ts:236-245`). It arrives as a normal `live` message from us;
   - otherwise reply `ZrdtResend{groupId, record, opening}` 1:1, with the opening from
     `zrdtOpening` if we still hold it. Include the opening only if the requester was a member
     when the record was sent; otherwise send the record alone, as in a structure-only dump (A9,
     review §2.9). **[amendment]**

   Send one `ZrdtNotFound{groupId, digests}` for the digests we lack. Replies are always 1:1;
   never broadcast a reply. A new request type is needed because `onRetryRequest` is only reached
   from `decryptionErrorMessage`, which names `(sentAt, senderDevice)`, not a digest.
7. **On `ZrdtResend` (a relay):** `ACCEPT_RECORD(chat, record, opening)` **[amendment]**
   (protocol 2). It may report `MISSING` (go to step 3; the relay waits in `zrdt_pending` with
   its opening, which is checked again when it drains). On `BAD_OPENING`, call it again without
   the opening and keep the record as structure only. `MALFORMED`: drop and log. The returned
   digest names the gap row it fills. Provenance is `relayed(by responder)`, or `live` if the responder is the record's
   author. Re-enter Desktop at `handleDataMessage` with the opened DataMessage, through the scope
   predicate, with a flag that skips the zrdt step, and save it with the gap row's `received_at`.
   Show it as "relayed by Bob". An opening has no field 200 (`ZrdtMeta`, including `disown`), so a
   relayed or imported message never contributes a `disown` list; only live messages do. If the
   relay has **no opening** (the responder no longer holds the content, or the requester joined
   later), accept the record as structure only: it resolves the links, and the gap row becomes "a
   message from Alice (content unavailable)". **[amendment]**
8. **Relayed messages never apply side-effect fields.** `handleDataMessage.preload.ts:687-711` sets
   the sender's `profileKey` for group messages; a relay must not. The same goes for the expire
   timer, group changes and anything outside the scope predicate.
9. **Author fast path.** Once a relayed record arrives, the receiver knows its author. It sends
   `ZrdtResendRequest` 1:1 to the author, whose app re-sends the original through the sendLog
   (step 6). That copy arrives `live`, so the message is confirmed by its author at once. Limits:
   the sendLog serves only within 24 h. It is pruned per recipient on delivery receipts, but a
   member who never acknowledged the message keeps its entry, which is the case that matters.
   **Wave 2 finding** **[amendment]**: on one machine the fast path is so quick that "relayed by
   Bob" is replaced by "confirmed by Alice" before anyone (or `demo/smoke.ts`) sees it; the
   status records `wasRelayed: true` with provenance `live`. Beat 2 needs the relayed label on
   screen for a moment; wave 3 fixes this in the fork (TODO: hold the fast path for the demo
   delay, or show "relayed by Bob, confirmed by Alice").
10. **Upgrade, never drop.** If the author's live copy arrives later (fast path or a delayed
    original), it upgrades the provenance of the same digest to `live`. Desktop's
    `(sent_at, sourceServiceId)` dedupe (`handleDataMessage.preload.ts:124-145`) must never silently
    drop a copy whose digest differs. On upgrade, take the `disown` list from the live copy only.
    **[amendment]**
11. **`ZrdtNotFound` is not decisive.** The server can drop the request or the reply. An honest
    member may lack the record: another of their devices linked it, or their store was salvaged,
    relinked or erased. A not-found from a member for a digest that member linked is evidence of
    inconsistency, not of malice. The gap row then says "still missing", with "Ask again".
12. **Never refuse a record in your own name.** Refusing would stall everything that links it. If
    a record with our ACI as author arrives that we did not create, accept it, alarm locally
    ("Someone linked a message in your name that you did not send"), and add its digest to our
    disown set. **Every** later message carries the full set in `ZrdtMeta.disown`, so a member
    who missed one of our messages (dropped by the server) still sees the disown in the next one.
    The other members' `CLASSIFY` then shows it as "not confirmed by" us. **[amendment]**

**[amendment]** Do not reuse `ts/services/retryPlaceholders.std.ts` for gaps: it is invisible
bookkeeping and refuses to reposition a message once the conversation has been opened (review
§2.7). Use the `zrdt-gap` row (§6).

**Blocking** is a permanent divergence in both directions: for example, group sends skip members
we blocked (`SendMessage.preload.ts:1222-1236`). Document it. **[amendment]**

## 6. Persistence

**[amendment]** Dedicated SQL tables, added by a migration in `ts/sql/migrations` with
`ts/sql/Server.node.ts` and `ts/sql/Interface.std.ts` (see `DATABASE_SCHEMA.md`):

- `zrdt_records(conversationId, digest, record, PRIMARY KEY(conversationId, digest))`: append-only
  apart from the rewrite after `SALVAGE` (Startup, below), structure only, one row per accept.
- `zrdt_pending(conversationId, digest, record, messageId)`: the pending buffer. It must be
  persisted. If it is lost, a message already in the DB has no record, and later messages that
  link it show gaps the client caused itself.
- `zrdt_provenance(conversationId, digest, kind, byAci, disownedBy)`.

Load them lazily per conversation.

**Not `items`.** **[amendment]** `items` values are `JSON.stringify`'d, so a `Uint8Array` reloads
as `{"0":…}` after a restart, and every item is loaded into memory and mirrored into Redux at
startup. Also, `window.storage` does not exist: the API is `itemStorage`
(`ts/textsecure/Storage.preload.ts:144`), and its keys are a closed typed union
(`StorageKeys.std.ts:73`), so per-conversation keys will not typecheck.

**Content: `zrdtOpening`.** **[amendment]** The opening (nonce ‖ DataMessage bytes without fields 15 and 200, §3) is a new message
attribute, `zrdtOpening`, marked `erase` in `messageAttributesEraseBehavior`. That table is
exhaustive, so TypeScript forces the choice, and Desktop's own delete, expiry and view-once paths
remove the opening. The store keeps structure only, never plaintext. Desktop itself keeps no
DataMessage bytes: it strips them before every DB write and never keeps them for received messages.

**Startup.** **[amendment]** Per group: `OPEN(chat, group, the records from zrdt_records)`.
- `OK` → proceed.
- `UNVERIFIABLE{unverifiable, missing}` → mark the conversation rejected and show the banner naming
  the missing digests ("message ·9ac1 is missing"). **Do not merge** anything into it until the
  user chooses "Keep what verifies" (`SALVAGE`: the store it loads is checked, the dropped digests
  are listed, and the kept records become `imported`) or "Import a copy from a member"
  (`RESTORE_PLAN.md`).
- `MALFORMED`, `TOO_LARGE`, `WRONG_CHAT` or `COLLISION{digest}` → the same banner, with the reason.

After `SALVAGE` at startup, rewrite the conversation's `zrdt_records` rows to the kept records in
one transaction: delete the rows of the dropped digests (keep the dropped list for the report).
Otherwise the next start runs `OPEN` on the same rows and shows the banner again. Rows are
append-only apart from this step. **[amendment]**

`zrdtd` holds only `CheckedStore` values, so no store exists that was not built by `NEW` and
`ACCEPT` or passed `OPEN`, `MERGE` or `SALVAGE`. The same re-`OPEN` runs whenever `zrdtd` restarts.

**What `OPEN` catches, and what it does not.** **[amendment]** It catches removing or altering a
record that something links, a link to nothing, a changed group, and malformed bytes. It does
**not** catch removing the newest record (a head), editing a head, or appending a forged record:
each leaves a valid history that ends somewhere else (`tail_replaced_passes_open`). Live messages
confirm or expose those later (§5, `RESTORE_PLAN.md`).

**Timeline placement.** **[amendment]** Desktop orders the timeline by `(received_at, sent_at)`,
and `received_at` is a local arrival counter, so a recovered message would land below the reply
that revealed it. On `MISSING` for message M:
- restamp M with a new counter;
- insert a new `zrdt-gap` message with M's old `received_at` and `sent_at = M.sent_at − 1` (this
  touches the `MessageType` union in `ts/model-types.std.ts:159-182`, `getPropsForMessage`,
  `isMessageEmpty` and the `TimelineItem` switch);
- save recovered records with the gap's `received_at`;
- delete the gap row once it resolves.

Multi-device: each device (phone, desktop) holds its own store. Sync messages carry links like
any other message, so a linked desktop accepts its primary's messages the same way. Stock
link-and-sync and Signal backups carry no zrdt data: a device restored that way has a full
timeline and an empty store, and matching its rows to records is out of scope. **[amendment]**

Disown and `notConfirmedByAuthor` assume one zrdt device per account. Records that arrive live
from your own ACI (sync transcripts) count as your own. A record from your other device that
arrives relayed or imported cannot be told apart from a forgery, so with two zrdt devices per
account the server could provoke a false disown. The demo has one zrdt device per account; the
mock phones do not run zrdt. **[amendment]**

## 7. UI changes (minimal, demo-first)

Component paths **(verified to exist; which one owns what, confirm on checkout)**. **[amendment]**
New zrdt components live in `ts/zrdt/ui/` with plain props and no imports from Signal's `ts/`, so
the fallback client can reuse them; the Signal files below only render them. Statuses come from
`CLASSIFY` and are stored when records are accepted; the UI renders stored values.

| UI piece | Where |
|---|---|
| Per-message code: 4-char tag in the metadata line; click → the digest's first 128 bits as ≥ 12 words, with "Copy" for the full digest **[amendment]** | `ts/components/conversation/MessageMetadata.dom.tsx` (tag), `MessageDetail.dom.tsx` (expanded) |
| Gap row: "1 message you haven't received. Bob replied to it." with a spinner → "requested" → "still missing", with "Ask again". It never says the server or a member is at fault **[amendment]** | new `ZrdtGapNotification.dom.tsx` modelled on `DeliveryIssueNotification.dom.tsx`; rendered by `TimelineItem.dom.tsx` for the `zrdt-gap` message type |
| Provenance labels **[amendment]**: "relayed by Bob" (relayed, not yet confirmed by its author); `confirmedByAuthor` shows as a normal message, and a message that was relayed first shows "confirmed by Alice"; "held by Alice" (`heldBy`: another member's live message reaches it); grey (`unconfirmed`); "not confirmed by Bob" (`notConfirmedByAuthor`) | `TimelineMessage.dom.tsx`, `MessageMetadata.dom.tsx` |
| Own-name alarm: "Someone linked a message in your name that you did not send." The digest goes into the disown set that every later message carries **[amendment]** | conversation-level banner, beside the rejected banner |
| Rejected banner (conversation-level): "This copy of the chat does not verify: message ·9ac1 is missing", with "Keep what verifies" and "Import a copy". It names what is missing, not who is at fault: a corrupted or truncated copy fails the same way **[amendment: names the `missing` digests]** | new `ZrdtRejectedBanner.dom.tsx`, rendered above `Timeline.dom.tsx`; wire via `ts/state/ducks/conversations.preload.ts` |
| "zrdt unavailable" banner when `zrdtd` exits; the backend's kind and version always on screen **[amendment]** | same banner slot |
| Compare: "Copy compare code" / "Paste compare code". The code carries the full sorted heads set; ≥ 12 words are shown only as an "equal?" fingerprint. No QR: Desktop cannot decode QR codes, and on one machine the clipboard is shared **[amendment]** | new `ZrdtCompareModal.dom.tsx` modelled on `ts/components/SafetyNumberModal.dom.tsx`; button in `ConversationHeader.dom.tsx`; state in `ts/state/ducks/globalModals.preload.ts` |
| Import / Export history (`RESTORE_PLAN.md`) **[amendment]**. Export: the store blob plus a content section keyed by digest, after OS authentication and a "do not share" warning; content left out for `expireTimer > 0`, deleted-for-everyone and view-once; structure only for anyone who joined after a record was sent. Openings never contain field 15 (`groupV2`, which holds the group master key; §3), so the dump carries no master key, and the importer takes the group from the conversation it imports into (`RESTORE_PLAN.md` §3, update §4.5). Import: `MERGE` (it runs `OPEN` on the file first); every content entry must satisfy `COMMIT(opening) == record.commit`, and entries of the excluded kinds are refused. If the file fails, the banner offers "Keep what verifies" (`SALVAGE`). If the chat already has a store, run `SALVAGE` under a scratch chat key, `ENCODE` that store, `MERGE` the blob into the open store, then `CLOSE` the scratch key: the open store only grows. Records it already held keep their provenance; only records new to it start `imported` | Settings → Internal (`PreferencesInternal.dom.tsx`, enabled in the mock setup) for the demo; conversation menu later |
| Unconfirmed section **[amendment]**: imported and salvaged records start `imported`. Until confirmed they sit in one collapsed section, "N messages not yet confirmed by any member", without avatars or live links, never inline under a member's name | `Timeline.dom.tsx` |
| Optional, cut from the demo criteria, live records only **[amendment]**: "confirmed by" (formerly "seen by": members whose live records reach a message, via `REACH_SET`). It means those members hold the message, not that its author wrote it, and it must not look like the author label "confirmed by Alice"; fork marker on `(author, sent_at)` with different digests | `TimelineMessage.dom.tsx` |

**Say plainly** (UI and README): an exported dump leaves Signal's encryption; the structure of
expired messages (authors, causal shape, count) stays in the store; links are receipts the whole
group can see. **[amendment]**

**Compare screen logic.** **[amendment]** Given our store `S`, our heads `H` and their heads `H'`
(pasted from their compare code, which carries the full set):

- `H' = H` → **identical**: the same set of messages, or two records collide
  (`CheckedStore.agree`).
- `H' ≠ H` and every `h' ∈ H'` is in `S` (`HAS`) → **they're behind**: you already hold everything
  their code points at.
- some `h' ∉ S` → **you're behind**: request those digests 1:1 from the code's owner, then from the
  group; when they arrive, compare again.
- still missing after the timeout → **"Bob has 1 message you don't (·k7f2). Asked; no answer."**,
  with "Ask again". This names an inconsistency, not a culprit: a member can link a made-up digest,
  and an offline author looks the same (review §4).

Word list: a BIP-39 style 2048-word list; ≥ 12 words = 128 bits of the digest, only for an
"equal?" check by eye. 88 bits would resist the server, but a malicious member could grind a
match with about 2^44 work (review §3.3). The pasted code always carries the full set. Full digest
behind a click. **[amendment]**

## 8. The villain

**[amendment]** The beats need a server that can drop one group message to one member (beat 2) and
discard everything sent to a member (beat 3). `hold`/`release` is kept for rehearsal and questions.
Two ways to get one.

### 8a. Evil mock server (recommended)

**Hook points** (review §3.1). **[amendment]** All deliveries to linked desktops go through
`Server.handleMessage` (`src/api/server.ts:733`), then `Server.send` (`src/server/base.ts:1017`).
That covers 1:1 websocket sends, gRPC sealed-sender multi-recipient sends, sync messages, receipts,
and queued delivery on reconnect. **Do not override `send()`**: it also carries the fake phones' own
traffic (`PrimaryDevice` is built with `send: this.send.bind(this)`), and inside it neither the
source nor the recipient set is visible. Override `handleMessage` (for `deviceId ≠ 1`) plus
`prepareMultiDeviceMessage`, which sees every recipient of a multi-recipient send. A sketch from the review exists, kept outside the repo (`~/devel/zrdt-review-spikes` on the reviewer's machine) (untested; key its recipient sets by more
than the timestamp, because sender-key distribution fan-outs share one `Date.now()`).

```ts
class EvilServer extends Server {
  rules: Array<Rule>;   // dropGroupMsg(from, to) | blackhole(to) | hold(to) / release(to)
  override async prepareMultiDeviceMessage(...args) {     // note every recipient of this send
    this.noteRecipient(args);
    return super.prepareMultiDeviceMessage(...args);
  }
  override async handleMessage(source, kind, type, target, encrypted, timestamp) {
    const deliver = () => super.handleMessage(source, kind, type, target, encrypted, timestamp);
    if (target.deviceId === 1) return deliver();            // fake phones: untouched
    const seen = this.describe(target, source, timestamp, encrypted);  // to, inferred from, recipients
    return this.apply(seen, deliver);                        // pass | drop | hold
  }
}
```

**Rules.** **[amendment]**
- `dropGroupMsg(from, to)`: drop once, matching a send with ≥ 2 recipients and the inferred
  sender. "The next envelope to Carol" is not enough: a read receipt, a delivery receipt or a
  sender-key distribution message can use it up, and a dropped sender-key distribution message is
  healed by Signal's own `senderKey.retry`, which would spoil the beat.
- `blackhole(to)`: discard everything sent to a member (do not queue it).
- `hold(to)` / `release(to)`: queue, then deliver.

Arm rules only after the warm-up sends. There is no `replay` rule (Signal discards replays as
`DuplicatedMessage`, then dedupes) and no `reorder` rule.

**What the server can see.** **[amendment]** A rule may only use what a real Signal server sees:
recipient account and device, envelope type, timestamp, size, and the recipient set of a
multi-recipient send. Under sealed sender the server can still infer the sender: the recipient set
is the group minus the sender, and the sender's own authenticated `SyncMessage.Sent` carries the
same timestamp within about a second. So "drop Alice's message to Carol" is a fair server power.
The mock process holds every key, so "the real server's power" is a policy the rules follow, not a
property of the mock.

Controls: a tiny HTTP panel (`/rules`, `/log`) or REPL. The rules are pure functions in
`demo/rules.ts` with two adapters: `EvilServer`, and the websocket relay of the fallback client
(§10). **[amendment]**

**Launch harness.** **[amendment]** `demo/launch.ts` is new work, not a thin reuse: about 300–400
lines, phase E 1.5–2 days. No existing test puts two or more desktops in one group; only
`twoClients` shares a server, and it is 1:1. Run it with `node --import tsx demo/launch.ts`. It
reuses `ts/test-mock/bootstrap.node.ts` and injects config through the `SIGNAL_CI_CONFIG` env var
the test harness already uses (`serverUrl`, `storageUrl`, `cdn`, `ciMode`, `storageProfile`,
`updatesEnabled: false`) **(verified, `bootstrap.node.ts`, `playwright.node.ts`)**. Checklist:

1. One `EvilServer`.
2. **Four** `Bootstrap`s sharing it (Alice, Bob, Carol, Dave), each with `contactCount: 0` (the
   default adds ten fake contacts each; four Bootstraps would create about 244 fake devices) and a
   patched `phoneName` (otherwise every phone is named `'Myself'`).
3. `ciMode: 'full'`. It is required: `link()` needs `window.SignalCI`, and with `false` it spins
   in a tight loop. Its side effects are harmless, but its retry backoff is 10× shorter, so the
   zrdt timeouts get explicit demo values.
4. Group "Camping" with all four members from creation, and the group plus the other members in
   **every** phone's storage state
   (`StorageState.getEmpty().updateAccount(…).addGroup(group, {whitelisted: true})…`);
   `helpers.createGroup` only writes the creator's.
5. Link Alice's, Bob's and Carol's desktops one after another, then tile the windows
   (`BrowserWindow.setBounds`). Each desktop sends one warm-up message, so sender keys are
   distributed before beat 1. Arm rules only after that.
6. Dave's phone receives beats 1–4; his desktop is linked just before beat 5.
7. To restart a desktop, use `await app.close(); await app.start();`. **Never**
   `bootstrap.startApp()`: if a start fails once, it deletes the profile and silently relaunches
   unlinked.

The remote-config flag `desktop.senderKey.retry` is enabled by the bootstrap **(verified)**; keep
it. It only fires on decryption errors, so drops are not silently healed, and our resend flow sits
beside it.

Day-1 spike for lane H3: desktops exchange sender-key group messages through the mock's gRPC
multi-recipient route. That is the one real unknown. **[amendment]**

What this does *not* show: "the real Signal server". The script is the same code Signal runs its
own integration tests against, which is a fair answer, and the fork's own code paths are
identical. If a judge wants prod, 8b.

### 8b. Evil proxy against staging (stretch)

A TLS-terminating reverse proxy between the fork and `chat.staging.signal.org`.

- Fork config: `serverUrl` → `https://proxy.local:8443`; `storageUrl` and `cdn` left pointing
  at staging (passthrough); the proxy's CA goes into `certificateAuthority` (a PEM string in
  `config/*.json`) **(verified keys)**. `WebAPI.preload.ts` passes `certificateAuthority` both
  to its HTTPS agent (`ca:`) and to `libsignalNet` (`Net`) **(verified)**; **verify** that
  libsignal-net honours the custom CA for the chat websocket, since the websocket now lives in
  Rust. If it does not, 8b is off: `SIGNAL_ENABLE_HTTP` is no way around it, because it never
  touches `serverUrl`, the HTTPS agent or libsignal-net (review §5.2). **[amendment]**
- `proxyUrl` in config is an HTTP CONNECT proxy option **(verified)**; it tunnels TLS, so it can
  only drop whole connections, not envelopes. Not sufficient on its own.
- What the proxy sees: which device connected, websocket frames (`PUT /api/v1/message` per
  envelope, confirm framing on checkout), timing, sizes. What it cannot see: content. Under sealed
  sender it does not see the sender directly, but it can infer it as in 8a. **[amendment]**
- Controls: same rule set as 8a, applied to frames per authenticated device connection; forward
  keepalives, auth headers, and all other REST calls untouched.
- Production builds clear `NODE_CONFIG`/`NODE_APP_INSTANCE` **(verified, `app/config.main.ts`)**,
  so this only works in dev builds. Never point a dev fork at production with a phone that
  matters: it unregisters the phone **(verified, CONTRIBUTING)**.

## 9. Demo script (target: beats in under 4 minutes, whole demo within 5)

**[amendment]** Five beats: 30 + 60 + 45 + 40 + 60 = 235 s. That leaves time for the intro and the
proof pitch within the 5-minute limit.

Pre-demo checklist: **[amendment]** `zrdtd` built on the Mac, and the backend showing `lean` and its
version, with `ZRDT_REQUIRE_LEAN=1`; fork built with `pnpm run generate`; `demo/launch.ts` has
brought up Alice, Bob and Carol in a fresh group "Camping" (Dave a member from creation, his
desktop not yet linked), warm-up messages sent, no rule armed; windows tiled; stores empty apart
from the warm-ups; `ZRDT_RESEND_DELAY_MS` at 3–5 s; the villain panel in a terminal.

**Beat 1, codes match (30 s).** **[amendment]** Alice: "who's bringing the tent?" Bob: "me". Carol:
"I have the stove". Expected: the last message shows the same code on all three screens. Bob
clicks "Copy compare code"; Carol clicks "Paste compare code": **identical**.

**Beat 2, gap (60 s).** **[amendment]** Villain: `dropGroupMsg(alice, carol)`. Alice: "actually I
lost the tent poles". Bob (who got it) sends a *plain* reply, not a quote-reply, which would show
the dropped text: "I'll bring spares". Expected: Carol's screen shows Bob's message *and* a gap row
above it: "1 message you haven't received. Bob replied to it." It stays for 3–5 s
(`ZRDT_RESEND_DELAY_MS`). Carol's app asks Bob; Alice's message appears in place, labelled
"relayed by Bob". Carol's app then asks Alice, whose app re-sends the original; the label becomes
"confirmed by Alice". Point out: Carol was told, and recovered, without trusting the server.
Desktop does not otherwise recover a dropped group message, so this is zrdt's doing (review §3.3).

**Beat 3, withheld (45 s).** **[amendment]** Villain: `blackhole(carol)`. Alice: "meet at 9 at the
trailhead". Nobody replies. Expected: Carol's screen shows nothing. This is the limit that links
alone cannot catch (`withheld_tail_undetectable`). Bob clicks "Copy compare code"; Carol pastes it.
Carol's app asks for the digest, waits for the timeout, then shows "Bob has 1 message you don't
(·k7f2). Asked; no answer." Clear the villain; "Ask again" recovers it. Point out: Carol now knows
she is missing a message. zrdt does not say who is at fault.

**Beat 4, doctored restore (40 s).** **[amendment]** In Carol's Settings → Internal, export the
store. `demo/doctor.ts` removes a **linked, non-head** record (decode, remove, re-encode). Import
it: `OPEN` fails, and the red banner reads "This copy of the chat does not verify: message ·9ac1 is
missing" (from the `missing` list). "Keep what verifies" lists what was kept and dropped; Carol's
own chat does not change, because she already holds every kept record (§7, Import). Present it as
"a tampered restore is caught", not as a server attack. No on-disk edit: the DB is SQLCipher.
Removing or editing the newest message, or appending a fake, would pass `OPEN`; beat 5 shows how
live messages catch an appended fake.

**Beat 5, restore from anyone (60 s, doctored variant only).** **[amendment]** `RESTORE_PLAN.md` §6.
Link Dave's desktop. Dave imports Bob's export, onto which `doctor.ts` has automatically appended
two fakes attributed to Bob, on top of the genuine head (digests depend on the live run, so the file
cannot be made in advance). Expected: everything collapsed and grey, "N messages not yet confirmed
by any member". Alice writes: the genuine history becomes "held by Alice", and Alice's own messages
"confirmed". Bob writes: Bob's genuine messages are confirmed, and the two fakes are marked "not
confirmed by Bob".

**Close** **[amendment]** with: Signal already stops the server from reading or forging messages.
On top of that:

> A server cannot make a member's app accept a history with a hole in it: if any later message
> builds on one you lack, you are told and it is fetched. Two members can confirm with one code
> that they hold the same set of messages; once the server splits a group it can never merge it
> back without the gap showing. The server can still delay, hold back the newest messages until
> someone replies or members compare, and deliver concurrent messages in different orders.

"A stock client keeps working" is a stretch: the mock setup has no stock client, because every
Bootstrap launches the fork. **[amendment]**

## 10. Risks and fallbacks

| Risk | Mitigation |
|---|---|
| Fork build breakage **[amendment]** | Pinned to `v8.33.0` (Electron 44.9.1, Node 24.22.0, pnpm 11.24.0); recorded in `PLAN.md` |
| `zrdtd` crashes, panics or is missing **[amendment]** | Fail closed: "zrdt unavailable" banner, nothing marked accepted, re-`OPEN` from SQL rows on restart; `LEAN_ABORT_ON_PANIC=1`; the decoder never sizes an allocation from an untrusted count (fuzz vector) |
| Frame protocol bugs (short reads, reply order) **[amendment]** | Read until a whole frame has arrived; replies in request order; rung 7 compares the TS stub with `zrdtd` on the Mac |
| In-process `.node` (macOS stretch only) **[amendment]** | 2-hour time box on day 1; copy every output; guard every entry; throw on load failure, never a no-op |
| Mac environment **[amendment]** | Launch from the GUI session (Aqua, Keychain); Xcode CLT; fetch the Electron binary ahead of time; agent access by SSH key or Claude Code on the Mac. Still open: chip and RAM for four Electron instances plus the mock server, and whether the Mac mini is the demo machine |
| Four instances on one machine **[amendment]** | Mock-server launch gives separate temp profiles **(verified)**; `contactCount: 0`; else `NODE_APP_INSTANCE` with one `config/local-<name>.json` each |
| Certificate pinning / libsignal-net custom CA **[amendment]** | 8a avoids it entirely; for 8b, verify the custom CA first, as there is no HTTP way around it |
| Account provisioning (numbers, SMS, captcha, registration lock) | 8a needs none; for 8b use staging standalone registration and prepare numbers a day early |
| Staging rate limits or odd-traffic blocks | 8b only; keep traffic to a handful of messages; never touch production |
| Unknown proto fields rejected somewhere **[amendment]** | Stock Desktop ignores the unknown `DataMessage` field **(verified in `handleDataMessage`)**, and logs and drops unknown `Content` messages; no stock client runs in the mock setup |
| `ciMode` changing UI behaviour **[amendment]** | `'full'` is required; its side effects are harmless apart from the 10× shorter retry backoff, so zrdt timeouts are explicit |
| A villain rule hits the wrong envelope **[amendment]** | `dropGroupMsg` matches ≥ 2 recipients and the inferred sender; arm rules only after the warm-up sends |
| Relayed records misattributed **[amendment]** | Three provenance values; only `live` records confirm authorship; relays never apply side-effect fields; disown for records in your own name |
| Recovered message lands below the reply **[amendment]** | `zrdt-gap` row and restamping (§6) |
| UI blames the server without proof **[amendment]** | Gaps and "withheld" do not prove server fault; word them as "a message Bob has that you haven't received" |
| Privacy of exports and links **[amendment]** | Erasable openings; exports need OS authentication and leave out disappearing, deleted and view-once content; say plainly what leaves Signal's encryption and what persists (§7) |
| No mock CI on a public fork **[amendment]** | Signal's test-mock job is gated on the private repository; run the gates locally on the Mac |

**Hard fallback.** **[amendment]** The go/no-go is checkpoint F2 on day 3 (`PLAN.md` has F0–F4):
`demo/smoke.ts` (Playwright) passes, with three sends, the same digests everywhere, and `MISSING`
after a drop. If it is not green, start `demo/mini-client` on day 4 with 2 days: a minimal
Electron chat (one window per member, plaintext JSON over a websocket relay of about 100 lines that
applies the same `demo/rules.ts`), reusing `zrdtd` through `ZrdtBackend` and the `ts/zrdt/ui`
components. The Lean deliverable, the five beats and the villain's rules are unchanged; only the
transport is not Signal. Decide at the gate, not later.

## 11. Android stretch

**[amendment]** Signal-Android fork. `zrdtd` would need an Android build, or the in-process stretch
as a JNI shim over the same Lean `handle`. Same `SignalService.proto` change (the proto is shared
across clients). The commitment must be computed over the bytes as received: never re-encode
another client's bytes. Touchpoints to confirm on checkout: incoming `MessageContentProcessor`
(accept, pending buffer), outgoing `MessageSender`/`PushGroupSendJob` (heads → links),
`ConversationAdapter` for the code tag and gap row, a `ConversationSettings` entry for Compare.
Build config: service URL and trust store per CONTRIBUTING's "point its service URL to
`chat.staging.signal.org`" note **(verified)**; emulator traffic through the villain via
`-http-proxy` or by pointing the service URL straight at 8a's mock server (which already serves
provisioning and CDN endpoints). Only start this after beats 1–5 run on Desktop.
