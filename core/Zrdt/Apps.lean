import Zrdt.AppBase
import Zrdt.Torrent
import Zrdt.Git

/-!
# Protocol 5: the dispatcher (docs/apps/BUILD_M1.md §B)

**Owner: lane base.** Lanes torrent and git never edit this file: their hooks
(`Torrent.parse`, `Torrent.run`, `Git.parse`, `Git.run`) are wired here already.

`zrdtd` answers each payload with `Apps.handle` (`Zrdtd/Main.lean`). A request whose op byte is
in a lane's range goes to that lane's parser and runner: base `0x17`-`0x1F`, torrent
`0x20`-`0x27`, git `0x28`-`0x2F`. Every other op byte is protocol 4 (`Proto.Request.parse`,
`Proto.run`), unchanged; an op byte a lane does not define replies `UNKNOWN_OP`.

Protocol-4 requests run on `State.chats` exactly as `Proto.run` runs them, so every theorem of
`Proto.lean` holds of them. A protocol-4 request that names a **piece key** (a key of
`State.pieces`) runs on the piece stores instead: the read-only ops (`HEADS`, `HAS`, `GET`,
`REACH_SET`, `CLASSIFY`, `ENCODE`, `SERVE`, `ADDRESSED`, `LINKABLE`) unchanged, `CLOSE` removes the
store and its context, `NEW`, `NEW_RELATIVE`, `OPEN` and `SALVAGE` reply `CHAT_OPEN`, and the
other mutating ops (`ACCEPT`, `ACCEPT_RECORD`, `ACCEPT_VIEW`, `MERGE`) reply `BAD_REQUEST`. So a
piece store holds only what lane base's ops put there (BUILD_M1 §B.4, the guard).
-/

namespace Zrdt.Apps

open AppBase

/-- A protocol-5 request. -/
inductive Request
  /-- A protocol-4 request (op `0x01`-`0x16`). -/
  | v4 (q : Proto.Request)
  /-- A base op (`0x17`-`0x1F`). -/
  | base (q : AppBase.Request)
  /-- A torrent op (`0x20`-`0x27`). -/
  | torrent (q : Torrent.Request)
  /-- A git op (`0x28`-`0x2F`). -/
  | git (q : Git.Request)

/-- A protocol-5 reply. -/
inductive Reply
  /-- To a protocol-4 request. -/
  | v4 (r : Proto.Reply)
  /-- To a base op. -/
  | base (r : AppBase.Reply)
  /-- To a torrent op. -/
  | torrent (r : Torrent.Reply)
  /-- To a git op. -/
  | git (r : Git.Reply)

/-- The request's payload. -/
def Request.write : Request → ByteArray
  | .v4 q => q.write | .base q => q.write | .torrent q => q.write | .git q => q.write

/-- The reply's payload. -/
def Reply.write : Reply → ByteArray
  | .v4 r => r.write | .base r => r.write | .torrent r => r.write | .git r => r.write

/-- The lane that owns op byte `op`, as a parser of its body: `none` for a protocol-4 op byte,
`some none` for an op byte of a lane's range that the lane does not define. -/
def laneParser (op : UInt8) : Option (Option (Proto.Parser Request)) :=
  if 0x17 ≤ op ∧ op ≤ 0x1F then some ((AppBase.parse op).map (Request.base <$> ·))
  else if 0x20 ≤ op ∧ op ≤ 0x27 then some ((Torrent.parse op).map (Request.torrent <$> ·))
  else if 0x28 ≤ op ∧ op ≤ 0x2F then some ((Git.parse op).map (Request.git <$> ·))
  else none

/-- The status a request gets when it cannot be read: `UNKNOWN_OP` or `BAD_REQUEST`. -/
def Request.parse (payload : ByteArray) : Except Proto.Code Request :=
  if h : 0 < payload.size then
    match laneParser payload[0] with
    | none => Request.v4 <$> Proto.Request.parse payload
    | some none => .error .unknownOp
    | some (some p) =>
      match p.run payload 1 with
      | some q => .ok q
      | none => .error .badRequest
  else .error .badRequest

#guard (match Request.parse ⟨#[0x17]⟩ with | .error .unknownOp => true | _ => false)
#guard (match Request.parse ⟨#[0x30]⟩ with | .error .unknownOp => true | _ => false)
#guard (match Request.parse ⟨#[0x01]⟩ with | .ok (.v4 .version) => true | _ => false)

/-- The chat key a protocol-4 request names, and whether the request only reads. -/
def chatKey? : Proto.Request → Option (String × Bool)
  | .new c _ | .newRelative c _ | .open c _ _ | .salvage c _ _ | .accept c _ _
  | .acceptRecord c _ _ | .acceptView c _ _ _ _ _ | .merge c _ | .close c => some (c, false)
  | .heads c | .has c _ | .get c _ | .reachSet c _ | .classify c _ | .encode c | .serve c _
  | .addressed c _ _ | .linkable c _ => some (c, true)
  | .version | .commit .. | .hash _ | .audience _ => none

/-- Carry out a protocol-4 request: on the chats as `Proto.run` does, or on a piece store (the
guard in the module header). -/
def runV4 (build : String) (s : State) (q : Proto.Request) : Proto.Reply × State :=
  match chatKey? q with
  | some (c, readOnly) =>
    if s.pieces.contains c then
      if readOnly then ((Proto.run build s.pieces q).1, s)
      else
        match q with
        | .close _ => (.ok, { s with pieces := s.pieces.erase c, ctxs := s.ctxs.erase c })
        | .new .. | .newRelative .. | .open .. | .salvage .. => (.code .chatOpen, s)
        | _ => (.code .badRequest, s)
    else
      let (r, t) := Proto.run build s.chats q
      (r, { s with chats := t })
  | none =>
    let (r, t) := Proto.run build s.chats q
    (r, { s with chats := t })

/-- Carry out a request: the reply and the new state. The torrent and git ops only read. -/
def run (build : String) (s : State) : Request → Reply × State
  | .v4 q => let (r, s') := runV4 build s q; (.v4 r, s')
  | .base q => let (r, s') := AppBase.run s q; (.base r, s')
  | .torrent q => (.torrent (Torrent.run s q), s)
  | .git q => (.git (Git.run s q), s)

/-- Answer one request payload: the reply payload and the new state. A request that cannot be
read gets `UNKNOWN_OP` or `BAD_REQUEST` and changes nothing. -/
def step (build : String) (s : State) (payload : ByteArray) : ByteArray × State :=
  match Request.parse payload with
  | .ok q => let (r, s') := run build s q; (r.write, s')
  | .error c => (c.write, s)

/-! ## The build -/

/-- The Lean sources of the protocol-5 modules, read when this file is compiled. It imports them
all, so a change to any of them rebuilds it. -/
def sources : List String := [
  include_str "AppBase.lean", include_str "Torrent.lean", include_str "Git.lean",
  include_str "Apps.lean"]

/-- The build text of `VERSION`: `Proto.buildIdOf` over these sources and then `mainSource` (the
source of `Zrdtd/Main.lean`), so it covers every module `zrdtd` runs. -/
def buildIdOf (mainSource : String) : String := Proto.buildIdOf (String.join sources ++ mainSource)

/-- The build text without the read loop's source, for the checks in this package. -/
def buildId : String := buildIdOf ""

/-- Answer a list of request payloads in order, starting from an empty state. -/
def session (payloads : List ByteArray) (build : String := buildId) : List ByteArray :=
  (payloads.foldl (fun (out, s) p => let (r, s') := step build s p; (r :: out, s'))
    (([] : List ByteArray), ({} : State))).1.reverse

-- Protocol-4 payloads get protocol 4's replies.
open Examples in
#guard session [(Proto.Request.new "c" group).write,
    (Proto.Request.acceptRecord "c" (encode a1) none).write,
    (Proto.Request.heads "c").write, ⟨#[0x17]⟩, ⟨#[0x2A, 1]⟩] ==
  Proto.session [(Proto.Request.new "c" group).write,
    (Proto.Request.acceptRecord "c" (encode a1) none).write, (Proto.Request.heads "c").write,
    ⟨#[0x17]⟩, ⟨#[0x2A, 1]⟩] buildId

/-! ## The daemon's state -/

/-- The state of the running `zrdtd`. -/
initialize state : IO.Ref State ← IO.mkRef {}

/-- `zrdtd`'s entry point: answer one request payload. `build` is the build text of `VERSION`
(`buildIdOf`). The state is taken out of `state` while `step` runs, so `step` holds the only
reference to it. -/
def handle (build : String) (payload : ByteArray) : IO ByteArray :=
  state.modifyGet fun s => step build s payload

end Zrdt.Apps
