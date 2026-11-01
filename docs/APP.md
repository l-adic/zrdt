# APP.md: integrating zrdt into Signal Desktop for the demo

Audience: whoever forks Signal Desktop, writes the villain (mock server or proxy), and runs the
demo. Companion documents: `PLAN.md` (phases, gates, who does what) and `PLAN_HUMANS.md` (the
theorems). This file is only about getting zrdt into a Signal client and on screen.

Facts below marked **(verified)** were checked against `signalapp/Signal-Desktop` `main` on
2026-10-31 (version `8.36.0-alpha.1`). Anything marked **confirm on checkout** is a best guess
from file names and must be checked in the editor before relying on it. The pinned commit the fork
starts from goes in `PLAN.md`.

## 0. The one-paragraph plan

Fork Signal Desktop. Add one proto field (`zrdt_links`) so every group message carries the
sender's heads. On send, ask `libzrdt` for the heads; on receive, hand the message to
`zrdt_accept`. Persist the store as a blob. Add five small UI pieces (code, gap row, compare screen,
rejected banner, checkpoint "seen by"). Run three desktops against a Signal server we control
and make it misbehave on cue. Signal keeps doing confidentiality and sender authentication; zrdt
adds completeness and consistency of the history.

## 1. Target and rationale

**Primary: Signal Desktop fork.** TypeScript, Electron 45, React 19 **(verified)**. Fast UI
iteration, native N-API modules already in-tree, server URL and trust roots are plain config.

**Stretch: Signal Android fork.** Phones are more compelling on stage, but NDK/JNI, long builds,
and emulator proxying cost days. Section 11.

**Accounts.** A Signal Desktop normally links to a phone. Two ways around needing three phones:

- **Mock server (recommended, section 8a).** The Desktop repo ships `packages/mock-server`
  (`@signalapp/mock-server` 27.0.0), a mock Signal server used by the `ts/test-mock` Playwright
  suite **(verified)**. Its `Bootstrap` class creates a fake primary device ("phone"), links a
  desktop to it, and several bootstraps can share one server (`new Bootstrap({ server:
  bootstrap1.server })`, as `ts/test-mock/messaging/twoClients_test.node.ts` does) **(verified)**.
  No phone numbers, no SMS, no rate limits, and we own delivery.
- **Staging (fallback for "it's the real Signal network").** Dev builds connect to
  `chat.staging.signal.org` by default (`config/default.json`) **(verified)**. `CONTRIBUTING.md`
  describes registering a dev desktop as a *standalone* device on staging with a phone number
  (Relink → Standalone → verify) **(verified)**; three numbers are needed, SMS/captcha applies.

**Several desktops on one machine.** `NODE_APP_INSTANCE=alice pnpm start` switches the data
directory to `Signal-aliceProfile` **(verified, CONTRIBUTING)**. The mock-server path launches
each instance with its own temp profile via Playwright's `_electron.launch` **(verified,
`ts/test-mock/playwright.node.ts`)**; windows are visible, Electron has no headless mode. Three
laptops are not required.

## 2. Build

Toolchain **(verified)**: Node `24.22.0` (`.nvmrc`), pnpm, Python 3, Xcode CLT on macOS.

```sh
git clone git@github.com:<org>/Signal-Desktop.git && cd Signal-Desktop   # the fork
nvm use
npm install -g pnpm
pnpm install        # builds native deps; postinstall runs electron:install-app-deps
pnpm run generate   # protos, JS, CSS (generate:phase-0, generate:phase-1)
pnpm start          # staging by default; NODE_ENV=production + config/local-production.json for prod (see CONTRIBUTING "Changing to production")
```

Dev loop: `pnpm run dev:transpile` and `pnpm run dev:styles` watch; restart the app to pick up
changes **(verified, CONTRIBUTING)**. Packaging: `pnpm run build` → `electron-builder`
26.11.1 **(verified)**; `SKIP_SIGNING_SCRIPT=1 pnpm run build` for unsigned local builds.

**Where `@zrdt/native` goes.** `pnpm-workspace.yaml` lists `packages/*` as workspace members, and
`packages/mute-state-change` is an in-tree N-API addon built with `node-addon-api` 8.5.0 +
`bindings` 1.5.0 + `binding.gyp` **(verified)**. Copy that layout:

```
packages/zrdt-native/
  package.json      name "@zrdt/native", deps node-addon-api + bindings
  binding.gyp       sources: addon.cc; libraries: libzrdt.a, libleanshared/Lean runtime, libsodium or a vendored sha256.c
  addon.cc          N-API wrappers, one per libzrdt function; all Buffer in / Buffer out
  index.mjs, index.d.ts
  prebuilt/<platform>/libzrdt.a   produced by the Lean build (PLAN.md owns that pipeline)
```

Electron rebuild is already wired through `electron:install-app-deps` in `postinstall`
**(verified)**. Confirm on checkout how `mute-state-change` is referenced from the main
`package.json` (`workspace:*` dependency) and mirror it.

**Day-1 stub.** `libzrdt-stub`: a C file implementing the same API with a linked list and a
vendored SHA-256, so the TypeScript integration and UI can be built before the Lean library
lands. Same `binding.gyp` with a `-Dzrdt_impl=stub` switch. Swapping in the real library must not
change any TypeScript.

## 3. Message mapping and wire format

A zrdt record is `(payload, links, author)`:

- `payload` = canonical bytes of `(sender timestamp u64, text body, attachment digests)`. Built by
  **zrdt's encoder on both ends** from those three inputs; the TypeScript never concatenates
  bytes itself. Attachment digest = `AttachmentPointer.digest` (32 bytes; confirm field name on
  checkout). Long bodies that Signal moves into `bodyAttachment` count as an attachment digest,
  with `body` empty; this must be the same rule on send and receive.
- `links` = the sender's heads at send time, from `zrdt_heads(store)` of that group's store.
- `author` = sender ACI, 16 bytes (`authorAciBinary`-style; the ACI is what sealed sender
  authenticates).

The digest (`zrdt_hash(payload, links[], author)`, SHA-256 over the canonical encoding) is
**never sent**. Each receiver recomputes it. If the sender and receiver reconstruct different
bytes, the message simply fails to link for others; that is a bug to catch with the differential
tests in `PLAN.md`, not a security event.

**Proto change** (`protos/SignalService.proto`; `DataMessage` uses tags 1–29 today, `Content`
up to 11 **(verified)**):

```proto
message DataMessage {
  // ... existing fields ...
  repeated bytes zrdt_links = 200;          // 32-byte digests; sender's heads at send time
}

message ZrdtResendRequest { repeated bytes digests = 1; }
message ZrdtResend        { bytes record = 1; bytes dataMessage = 2; bytes authorAci = 3; }

message Content {
  // ... existing fields ...
  optional ZrdtResendRequest zrdtResendRequest = 200;
  optional ZrdtResend        zrdtResend        = 201;
}
```

Links go in `DataMessage` so they are inside the same sender-key/pairwise ciphertext as the
body. The two control messages go at `Content` level, next to `DecryptionErrorMessage`, so a
stock client ignores them entirely instead of rendering an empty message. Stock clients ignore
unknown fields; confirm on checkout that `processDataMessage` keeps unknown fields out of
`isUnsupportedMessage` / `requiredProtocolVersion` logic (it keys on `requiredProtocolVersion`,
not on unknown tags **(verified, `ts/messages/handleDataMessage.preload.ts`)**).

`ZrdtResend.dataMessage` carries the original encoded `DataMessage` bytes so the receiver can
render it; the receiver re-derives the record from `(timestamp, body, attachment digests)` +
`zrdt_links` + `authorAci`, hashes it, and only then accepts. The responder is authenticated by
Signal; the *content* is authenticated by the hash matching what other members linked.

Protos are compiled by `pnpm run generate` into `ts/protobuf/` **(verified placeholder dir)**;
confirm the exact `generate:phase-0` script in `package.json` on checkout.

## 4. Send path

Touchpoints **(paths verified; function lines approximate, confirm on checkout)**:

- `ts/textsecure/SendMessage.preload.ts`: where the `DataMessage` proto is assembled. Add
  `zrdtLinks` to the message-options type and set `proto.zrdtLinks`.
- `ts/messages/send.preload.ts` (`send`, ~line 41): the outgoing job. Before building the proto,
  call `zrdt_heads(store)` for the conversation's store and pass them as `zrdtLinks`. After the
  send resolves, build the record and `zrdt_accept(store, payload, links, author)`; it must return
  `accepted` (our own links always resolve); persist. Desktop already stores the sent
  `dataMessage` bytes on the message model (~line 78) **(verified)**; keep them, `ZrdtResend` needs
  them.
- `ts/util/sendToGroup.preload.ts` (`sendToGroup` ~123, `sendContentMessageToGroup` ~191,
  `sendToGroupViaSenderKey` ~271) **(verified)**: no change; links ride inside the content.
- Own-device sync messages (`sendSyncMessage` in `send.preload.ts`) carry the same bytes, so a
  linked phone or second desktop gets the links for free.

Ordering rule: compute heads and accept **inside the per-conversation send queue** so two
rapid sends from one client link each other instead of both linking the same old heads.

## 5. Receive path

Touchpoints **(paths verified)**:

- `ts/textsecure/MessageReceiver.preload.ts`: decrypts and emits events. No zrdt logic here.
- `ts/textsecure/processDataMessage.preload.ts` (`processDataMessage`, ~line 642): normalises
  proto → internal shape. Add `zrdtLinks: Array<Uint8Array>`.
- `ts/background.preload.ts` (`onMessageReceived`, ~line 2631; `decryption-error` and
  `retry-request` listeners ~678–691) **(verified)**: add handlers for `zrdtResendRequest` and
  `zrdtResend` beside the retry-request handler.
- `ts/messages/handleDataMessage.preload.ts` (`handleDataMessage`, ~92; attributes built
  ~535–582) **(verified)**: after the message attributes are built and before save, call
  `zrdt_accept`.

Per incoming group message:

1. `r = zrdt_accept(store, payload, zrdtLinks, authorAci)`.
2. `{accepted, digest}`: set `zrdtDigest`, `zrdtStatus: 'accepted'`; drain the pending buffer
   (retry every pending message whose links are now present); persist.
3. `{missing, digests}`: set `zrdtStatus: 'pending'`, store the raw message in a per-conversation
   pending buffer (SQL `items` row or a small table), render the gap placeholder for each missing
   digest, and send `ZrdtResendRequest{digests}` to the group. Model this on the existing
   `desktop.senderKey.retry` flow in `ts/util/handleRetry.preload.ts` (`onRetryRequest` ~129
   resends the stored sent proto; `RETRY_LIMIT`; dedupe by key) **(verified)**. Reuse its dedupe
   and backoff; one request per digest per minute.
3b. `{collision, digest}` (`PLAN.md` §3.3): a different record with the same digest is already in
   the store. Set `zrdtStatus: 'collision'`, do not store it as a normal message, show it with the
   fork marker and the digest. With SHA-256 this never fires in practice; it exists so the
   library's behaviour matches the model's collision clause at the one place it is observable.
4. On `ZrdtResendRequest` from a member: for each digest with `zrdt_has(store, digest)`, reply with
   `ZrdtResend` (our stored `dataMessage` bytes, links, author). Reply only inside the group.
5. On `ZrdtResend`: reconstruct, `zrdt_accept`; on `accepted`, process the inner `DataMessage`
   through the normal path with a flag that skips the link step; drain pending.

`ts/services/retryPlaceholders.std.ts` **(verified)** is Desktop's existing "placeholder for a
message we're waiting on" service; extend or copy it for gap placeholders rather than inventing a
new one.

## 6. Persistence

Store one blob per group conversation, keyed by conversation id, written with
`zrdt_encode(store)` after every accept. Two options:

- `window.storage.put('zrdt.store.<conversationId>', bytes)`: the `items` key-value table behind
  `ts/textsecure/Storage.preload.ts` **(verified)**. Zero schema work; fine for the demo.
- A dedicated `zrdt_stores(conversationId, blob, heads)` table in `ts/sql/Server.node.ts` +
  `ts/sql/Interface.std.ts` (see `DATABASE_SCHEMA.md`) if blobs get large. Confirm on checkout
  whether `items` values have a size limit in the IPC layer (`ts/sql/cleanDataForIpc.std.ts`).

On startup, per group: `zrdt_decode(bytes)` then `zrdt_check(store)`. `ok` → proceed.
`missing(d)` or `unreachable(d)` → mark the conversation rejected, show the banner naming `d`,
and **do not merge** anything into it until the user chooses "re-fetch from a member" (which
rebuilds the store from `ZrdtResend` replies) or "discard local copy".

Multi-device: each device (phone, desktop) holds its own store. Sync messages carry links like
any other message, so a linked desktop accepts its primary's messages the same way.

## 7. UI changes (minimal, demo-first)

Component paths **(verified to exist; which one owns what, confirm on checkout)**:

| UI piece | Where |
|---|---|
| Per-message code: 4-char tag in the metadata line; click → full digest as 8 words + QR | `ts/components/conversation/MessageMetadata.dom.tsx` (tag), `MessageDetail.dom.tsx` (expanded) |
| Gap placeholder row: "1 message you haven't received. Bob replied to it." with a spinner → "requested" → "still missing" | new `ZrdtGapNotification.dom.tsx` modelled on `DeliveryIssueNotification.dom.tsx`; inserted by `TimelineItem.dom.tsx` |
| Rejected banner (conversation-level) | new `ZrdtRejectedBanner.dom.tsx`, rendered above `Timeline.dom.tsx`; wire via `ts/state/ducks/conversations.preload.ts` |
| Compare screen: our heads, their heads, outcome | new `ZrdtCompareModal.dom.tsx` modelled on `ts/components/SafetyNumberModal.dom.tsx`; button in `ConversationHeader.dom.tsx`; state in `ts/state/ducks/globalModals.preload.ts` |
| Checkpoint message + "seen by" | render in `TimelineMessage.dom.tsx` when body is exactly `checkpoint`; "seen by" = members whose latest accepted record satisfies `zrdt_reaches(store, latest, checkpointDigest)` |
| Fork marker | in `TimelineMessage.dom.tsx`: two accepted records with equal author and equal links but different digests → small "sent as two versions" label on both |

Compare screen logic, given our store `S`, our heads `H`, their heads `H'` (pasted, scanned, or
received in a `ZrdtResend`-style exchange):

- all of `H'` ⊆ `H` and `H ⊆ H'` → **identical**
- every `h' ∈ H'` has `zrdt_has(S, h')` → **they're behind**
- `H ⊆` their store (they tell us) and some `h' ∉ S` → **you're behind** → request resend
- some `h' ∉ S` and a resend request yields nothing within the timeout → **withheld**, show `h'`

Word list: BIP-39 style 2048-word list, 8 words ≈ 88 bits of the digest (enough that a server
cannot grind two histories to the same display). Full digest behind a tap.

## 8. The villain

The four demo beats need a server that can drop, delay, reorder, replay, and partition per
recipient. Two ways to get one.

### 8a. Evil mock server (recommended)

`@signalapp/mock-server`'s `Server.send(target, message)` is the single per-device delivery
point: it writes to the device's websocket or queues until it connects **(verified,
`src/server/base.ts` ~890)**. Incoming envelopes arrive through `Server.handleMessage` in
`src/api/server.ts` (~656) **(verified)**. Subclass:

```ts
class EvilServer extends Server {
  rules: Array<Rule>;   // dropNextTo(member) | delay(member, ms) | reorder(member) | replay(member) | partition(set)
  override async send(target, message) {
    for (const rule of this.rules) if (rule.applies(target, message)) return rule.act(this, target, message, super.send.bind(this));
    return super.send(target, message);
  }
}
```

About fifty lines. Controls: a tiny HTTP panel (`/rules`, `/log`) or REPL. Because the mock
server also issues the sealed-sender certificates and sees envelope framing, "replay" is a byte
copy of an earlier envelope and "partition" is a set of members whose envelopes to each other are
queued forever.

Launch: a `demo/launch.ts` script that reuses `ts/test-mock/bootstrap.node.ts`: one
`EvilServer`, three `Bootstrap`s sharing it, `createGroup` on the first phone with the other two
as members, `link()` each desktop. Config injected via the `SIGNAL_CI_CONFIG` env var that the
test harness already uses (`serverUrl`, `storageUrl`, `cdn`, `ciMode`, `storageProfile`,
`updatesEnabled: false`) **(verified, `bootstrap.node.ts` ~1189–1203 and
`playwright.node.ts` ~78–84)**. Try `ciMode: false` first so the UI behaves normally; confirm on
checkout what `ciMode: 'full'` disables. Remote-config flag `desktop.senderKey.retry` is enabled
by the bootstrap **(verified)**; keep it, our resend flow sits beside it.

What this does *not* show: "the real Signal server". The script is the same code Signal runs its
own integration tests against, which is a fair answer, and the fork's own code paths are
identical. If a judge wants prod, 8b.

### 8b. Evil proxy against staging

A TLS-terminating reverse proxy between the fork and `chat.staging.signal.org`.

- Fork config: `serverUrl` → `https://proxy.local:8443`; `storageUrl` and `cdn` left pointing
  at staging (passthrough); the proxy's CA goes into `certificateAuthority` (a PEM string in
  `config/*.json`) **(verified keys)**. `WebAPI.preload.ts` passes `certificateAuthority` both
  to its HTTPS agent (`ca:`) and to `libsignalNet` (`Net`) **(verified ~430, ~1663–1671)**;
  **verify** that libsignal-net honours the custom CA for the chat websocket, since the websocket
  now lives in Rust. If it doesn't, use `SIGNAL_ENABLE_HTTP=1 pnpm start` **(verified,
  CONTRIBUTING)** and run the proxy as plain HTTP in front of a TLS client to staging.
- `proxyUrl` in config is an HTTP CONNECT proxy option **(verified)**; it tunnels TLS, so it can
  only drop whole connections, not envelopes. Not sufficient on its own.
- What the proxy sees: which device connected, websocket frames (`PUT /api/v1/message` per
  envelope, confirm framing on checkout), timing, sizes. What it cannot see: content, or the
  sender under sealed sender.
- Controls: same rule set as 8a, applied to frames per authenticated device connection; forward
  keepalives, auth headers, and all other REST calls untouched.
- Production builds clear `NODE_CONFIG`/`NODE_APP_INSTANCE` **(verified, `app/config.main.ts`)**,
  so this only works in dev builds. Never point a dev fork at production with a phone that
  matters: it unregisters the phone **(verified, CONTRIBUTING)**.

## 9. Demo script (target: 3 minutes)

Pre-demo checklist: Lean library or stub built; fork built with `pnpm run generate`; villain
running; `demo/launch.ts` has brought up Alice, Bob, Carol with a fresh group "Camping"; all three
windows visible and arranged; stores empty; the villain panel on a fourth screen or terminal.

**Beat 1, honest (40 s).** Alice: "who's bringing the tent?" Bob: "me". Carol: "I have the
stove". Alice sends `checkpoint`. Expected: on all three screens the checkpoint shows the same
8-word code; Alice's checkpoint reads "seen by Bob, Carol" within a few seconds (after each
replies or any later message from them arrives). Open Compare on Bob and Carol: **identical**.

**Beat 2, drop + reply (45 s).** Villain: `dropNextTo(carol)`. Alice: "actually I lost the tent
poles". Bob (who got it): "I'll bring spares". Expected: Carol's screen shows Bob's message
*and* a gap row above it: "1 message you haven't received. Bob replied to it." with a spinner.
Villain rule expires (or is removed). Carol's client has sent `ZrdtResendRequest`; Bob's client
answers `ZrdtResend`; the gap row is replaced by Alice's message in place. Point out: Carol was
told, and recovered, without trusting the server.

**Beat 3, withheld tail (45 s).** Villain: `partition({carol})` for messages from Alice only.
Alice: "meet at 9 at the trailhead". Nobody replies. Expected: Carol's screen shows nothing
(this is the attack hash links alone cannot catch). Bob opens Compare, shows his code to Carol
(QR). Carol's app: **withheld: ·k7f2…** and "a message Bob has that the server will not deliver
to you". Villain off; Carol's resend request succeeds; message appears.

**Beat 4, doctored restore (40 s).** From the dev menu on Carol: "Export zrdt store". Edit the
blob with the provided `demo/doctor.ts` (removes one record). "Import zrdt store". Expected:
red banner "This copy of the chat was altered: message ·9ac1… is missing", conversation
read-only until "Re-fetch from a member", which rebuilds and clears the banner.

Close with the one line: Signal already stopped the server from reading or forging; what you
just saw is it being caught dropping, withholding, and rewriting.

## 10. Risks and fallbacks

| Risk | Mitigation |
|---|---|
| Fork build breakage (alpha `main`, Electron 45) | Pin to the latest tagged release instead of `main`; record the commit in `PLAN.md` |
| Native module ABI (Electron vs Node headers) | Follow `packages/mute-state-change` exactly; `electron:install-app-deps` already rebuilds workspace addons **(verified)** |
| Lean runtime in an Electron addon (GC init, symbol clashes) | Initialise the Lean runtime once in the addon's init; export only byte-oriented functions; stub first |
| Three instances on one machine | Mock-server launch gives separate temp profiles **(verified)**; else `NODE_APP_INSTANCE` |
| Certificate pinning / libsignal-net custom CA | 8a avoids it entirely; 8b has the `SIGNAL_ENABLE_HTTP=1` escape hatch to verify |
| Account provisioning (numbers, SMS, captcha, registration lock) | 8a needs none; for 8b use staging standalone registration and prepare numbers a day early |
| Staging rate limits or odd-traffic blocks | 8b only; keep traffic to a handful of messages; never touch production |
| Unknown proto fields rejected somewhere | Stock Desktop ignores unknown tags **(verified in `handleDataMessage`)**; confirm Android/iOS if a stock phone is in the group |
| `ciMode` changing UI behaviour | Try `ciMode: false`; otherwise accept and note it |

**Hard fallback.** If the fork is not sending and receiving linked messages by the decision
point in `PLAN.md`, build `demo/mini-client`: a minimal Electron chat (one window per member,
plaintext JSON over a websocket to the same `EvilServer` rule engine), reusing `@zrdt/native` and
the same React components for the five UI pieces. The Lean deliverable, the four beats, and the
villain are unchanged; only the transport is not Signal. Decide at the gate, not later.

## 11. Android stretch

Signal-Android fork. `libzrdt.a` + Lean runtime via NDK as a prebuilt, JNI shim exposing the same
functions as `@zrdt/native`. Same `SignalService.proto` change (the proto is shared across
clients). Touchpoints to confirm on checkout: incoming `MessageContentProcessor` (accept, pending
buffer), outgoing `MessageSender`/`PushGroupSendJob` (heads → links), `ConversationAdapter` for
the code tag and gap row, a `ConversationSettings` entry for Compare. Build config: service URL
and trust store per CONTRIBUTING's "point its service URL to `chat.staging.signal.org`" note
**(verified)**; emulator traffic through the villain via `-http-proxy` or by pointing the service
URL straight at 8a's mock server (which already serves provisioning and CDN endpoints). Only
start this after beats 1–4 run on Desktop.
