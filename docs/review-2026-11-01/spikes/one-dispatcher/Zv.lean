import Std.Data.HashMap
open Std

/-- all store state lives in Lean; no handles cross the boundary -/
initialize stores : IO.Ref (HashMap String (Array ByteArray)) ← IO.mkRef {}

/-- the single dispatcher shared by both transports: op 1 = append(body) to store "g", op 2 = count -/
def handle (req : ByteArray) : IO ByteArray := do
  if req.size == 0 then return ByteArray.mk #[0xff]
  match req[0]! with
  | 1 => stores.modify (fun m => m.insert "g" ((m.getD "g" #[]).push (req.extract 1 req.size)))
         return ByteArray.mk #[0]
  | 2 => let n := ((← stores.get).getD "g" #[]).size
         return ByteArray.mk #[0, n.toUInt8]
  | _ => return ByteArray.mk #[0xfe]

@[export zrdt_l_call] def call (req : ByteArray) : IO ByteArray := handle req

partial def loop (i o : IO.FS.Stream) : IO Unit := do
  let hdr ← i.read 4
  if hdr.size < 4 then return
  let n := (hdr[0]!.toNat <<< 24) ||| (hdr[1]!.toNat <<< 16) ||| (hdr[2]!.toNat <<< 8) ||| hdr[3]!.toNat
  let r ← handle (← i.read n.toUSize)
  let m := r.size
  o.write (ByteArray.mk #[(m >>> 24).toUInt8, (m >>> 16).toUInt8, (m >>> 8).toUInt8, m.toUInt8] ++ r)
  o.flush
  loop i o

def main : IO Unit := do loop (← IO.getStdin) (← IO.getStdout)
