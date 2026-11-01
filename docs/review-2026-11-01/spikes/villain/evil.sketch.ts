// UNVERIFIED SKETCH (not type-checked: no node/pnpm in the review environment).
// EvilServer for the zrdt demo, written against @signalapp/mock-server 27.0.0 as vendored in
// Signal-Desktop main @5dad34ad. Line refs are to packages/mock-server/src.
//
// Design rule: a rule may only look at fields a real Signal server sees:
// recipient account+device, envelope type, client timestamp, ciphertext size, and the
// recipient set of the multi-recipient send that carried it. The mock process also holds
// every fake phone's identity key and every group master key; rules must not use them.

import type { Device } from '@signalapp/mock-server';
import { Server, EnvelopeType } from '@signalapp/mock-server';
import type { ServiceIdKind } from '@signalapp/mock-server';

type Name = string; // 'alice' | 'bob' | 'carol' | ...

export type Seen = Readonly<{
  to: Name;              // recipient account (from target.aci)
  toDevice: number;      // target.deviceId (desktops are >= 2; phones never reach here)
  type: EnvelopeType;    // SealedSender for almost everything a desktop sends
  ts: bigint;            // sender-chosen timestamp (api/server.ts:781-782)
  size: number;          // ciphertext length
  from?: Name;           // only if inferable: unsealed source, or group-minus-recipients
  recipients: ReadonlySet<Name>; // all accounts that got an envelope with this ts
}>;

export type Verdict = 'pass' | 'drop' | 'hold';
export type Rule = Readonly<{
  id: string;
  match: (e: Seen) => boolean;
  verdict: Verdict;
  remaining?: number; // undefined = until cleared
}>;

export class EvilServer extends Server {
  public names = new Map<string, Name>();           // aci -> display name, set by launch.ts
  public group = new Set<Name>();                   // the demo group, set by launch.ts
  public rules: Array<Rule> = [];
  public log: Array<string> = [];
  private recipientsByTs = new Map<bigint, Set<Name>>();
  private held: Array<() => Promise<void>> = [];

  // Every send path (ws PUT /v1/messages/:id at server/ws/connection.ts:280, gRPC
  // multi-recipient at server/grpc.ts:274, gRPC sync at server/grpc.ts:360) calls this once per
  // recipient account before any delivery; record who shares a timestamp.
  public override async prepareMultiDeviceMessage(
    ...args: Parameters<Server['prepareMultiDeviceMessage']>
  ): ReturnType<Server['prepareMultiDeviceMessage']> {
    const [, targetServiceId, , timestamp] = args;
    const set = this.recipientsByTs.get(timestamp) ?? new Set<Name>();
    set.add(this.names.get(targetServiceId) ?? targetServiceId);
    this.recipientsByTs.set(timestamp, set);
    return super.prepareMultiDeviceMessage(...args);
  }

  // api/server.ts:733. Linked desktops go through here and then this.send (api/server.ts:773);
  // fake phones are handled in-process (api/server.ts:803-818) and are left alone.
  public override async handleMessage(
    source: Device | undefined,
    serviceIdKind: ServiceIdKind,
    envelopeType: EnvelopeType,
    target: Device,
    encrypted: Buffer<ArrayBuffer>,
    timestamp: bigint,
  ): Promise<void> {
    const deliver = () =>
      super.handleMessage(source, serviceIdKind, envelopeType, target, encrypted, timestamp);
    if (target.deviceId === 1) {
      return deliver();
    }
    const recipients = this.recipientsByTs.get(timestamp) ?? new Set<Name>();
    const to = this.names.get(target.aci) ?? target.aci;
    let from: Name | undefined = source ? this.names.get(source.aci) : undefined;
    if (!from && recipients.size >= 2) {
      // Sealed-sender group send: the sender is the one member not addressed.
      const missing = [...this.group].filter(m => !recipients.has(m));
      if (missing.length === 1) from = missing[0];
    }
    const seen: Seen = { to, toDevice: target.deviceId, type: envelopeType, ts: timestamp,
      size: encrypted.length, from, recipients };
    const rule = this.rules.find(r => r.match(seen));
    const verdict: Verdict = rule?.verdict ?? 'pass';
    if (rule && rule.remaining !== undefined) {
      const left = rule.remaining - 1;
      this.rules = this.rules.map(r => (r === rule ? { ...r, remaining: left } : r))
        .filter(r => r.remaining === undefined || r.remaining > 0);
    }
    this.log.push(`${new Date().toISOString()} ${from ?? '?'} -> ${to}.${target.deviceId} ` +
      `ts=${timestamp} ${encrypted.length}B group=${[...recipients].join(',')} ${verdict}` +
      (rule ? ` (${rule.id})` : ''));
    if (verdict === 'drop') return;
    if (verdict === 'hold') { this.held.push(deliver); return; }
    return deliver();
  }

  public release(): Promise<void> {
    const h = this.held; this.held = [];
    return Promise.all(h.map(f => f())).then(() => undefined);
  }
}

// The only rules the four beats need:
export const dropGroupMsg = (from: Name, to: Name): Rule => ({
  id: `drop ${from}->${to} once`, verdict: 'drop', remaining: 1,
  match: e => e.to === to && e.from === from && e.recipients.size >= 2,
});
export const blackhole = (to: Name): Rule => ({
  id: `blackhole ${to}`, verdict: 'drop', match: e => e.to === to,
});
// Optional extra beat (reorder): hold the next group message to `to`, release after the next.
export const holdNext = (to: Name): Rule => ({
  id: `hold next -> ${to}`, verdict: 'hold', remaining: 1,
  match: e => e.to === to && e.recipients.size >= 2,
});
