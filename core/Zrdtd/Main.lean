import Zrdt.Proto

/-!
# `zrdtd`: the stdin/stdout loop (docs/PLAN.md §3.3)

Reads request frames (`length (u32, big-endian) ‖ payload`) from stdin, answers each with
`Zrdt.Proto.handle`, and writes the reply frame to stdout before reading the next request, so
replies come in request order. Diagnostics go to stderr.

- A read may return fewer bytes than asked; `readExact` reads until the frame is complete.
- Reads are at most 64 KiB at a time, so a frame's claimed length never sizes an allocation by
  itself; memory grows only with the bytes that actually arrive.
- End of input between frames: exit 0. End of input inside a frame: a diagnostic, then exit 1.
- The host runs it with `LEAN_ABORT_ON_PANIC=1`, so a `panic!` stops it instead of going on with
  a default value. Without it, `zrdtd` warns on stderr at start.
-/

open Zrdt

/-- The most bytes one read asks for. -/
def chunkSize : Nat := 65536

/-- Read `n` bytes, appending them to `acc`. Stops early only at end of input, so the result is
shorter than `acc.size + n` exactly when the input ended. -/
partial def readExact (input : IO.FS.Stream) (n : Nat) (acc : ByteArray) : IO ByteArray := do
  if n = 0 then return acc
  let chunk ← input.read (min n chunkSize).toUSize
  if chunk.isEmpty then return acc
  readExact input (n - chunk.size) (acc ++ chunk)

/-- What one round of the loop found. -/
inductive Next
  /-- A whole request payload. -/
  | frame (payload : ByteArray)
  /-- End of input between frames. -/
  | done
  /-- End of input inside a frame; the text says where. -/
  | cut (why : String)

/-- Read one frame. -/
def readFrame (input : IO.FS.Stream) : IO Next := do
  let header ← readExact input 4 .empty
  if header.isEmpty then return .done
  match readU32? header 0 with
  | none => return .cut s!"the input ended inside a frame header ({header.size} of 4 bytes)"
  | some n =>
    let payload ← readExact input n (.emptyWithCapacity (min n chunkSize))
    if payload.size < n then
      return .cut s!"the input ended inside a frame ({payload.size} of {n} bytes)"
    return .frame payload

/-- A one-line description of a request that `zrdtd` could not carry out (a status of `0x80` or
more), for stderr. `none` for every other reply. -/
def describeRefusal (payload reply : ByteArray) : Option String := do
  let status ← reply[0]?
  guard (0x80 ≤ status)
  let code := ((Proto.Code.ofByte? status).map (·.name)).getD "?"
  let op := (payload[0]?.map fun b => (Proto.opName? b).getD s!"op 0x{hexOfBytes ⟨#[b]⟩}").getD
    "empty payload"
  pure s!"zrdtd: {op}, {payload.size} bytes: {code}"

/-- Answer frames until the input ends. Returns the exit code. -/
partial def loop (input output err : IO.FS.Stream) : IO UInt32 := do
  match ← readFrame input with
  | .done => return 0
  | .cut why =>
    err.putStrLn s!"zrdtd: {why}; exiting"
    return 1
  | .frame payload =>
    let reply ← Proto.handle payload
    if let some line := describeRefusal payload reply then err.putStrLn line
    output.write (u32be reply.size ++ reply)
    output.flush
    loop input output err

/-- Start `zrdtd`: one line to stderr, then the loop. -/
def main : IO UInt32 := do
  let err ← IO.getStderr
  if (← IO.getEnv "LEAN_ABORT_ON_PANIC") != some "1" then
    err.putStrLn "zrdtd: warning: LEAN_ABORT_ON_PANIC is not 1, so a panic would not stop zrdtd"
  err.putStrLn s!"zrdtd: protocol {Proto.protocolVersion}, {Proto.buildId}"
  loop (← IO.getStdin) (← IO.getStdout) err
