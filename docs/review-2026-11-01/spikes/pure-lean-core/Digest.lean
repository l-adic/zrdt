import Std.Data.HashMap
import ZCore.Sha256

namespace ZCore

/-- 32-byte digest as a structure (data field + proof). -/
structure Digest where
  bytes : ByteArray
  size_eq : bytes.size = 32
deriving DecidableEq

instance : Inhabited Digest := ⟨⟨ByteArray.mk (Array.replicate 32 0), by decide⟩⟩
instance : Hashable Digest := ⟨fun d => hash d.bytes⟩

/-- Same thing as a Subtype. -/
abbrev DigestS := { b : ByteArray // b.size = 32 }

/-- Pure-Lean hash, packaged as a Digest. -/
def sha256 (b : ByteArray) : Digest :=
  let r := Sha256.sha256 b
  if h : r.size = 32 then ⟨r, h⟩ else default

/-- C-implemented hash (extern + opaque), as in PLAN §4 Phase B. -/
@[extern "zrdt_sha256_c"]
opaque sha256C (b : @& ByteArray) : Digest

theorem sha256C_det (b : ByteArray) : sha256C b = sha256C b := rfl

end ZCore
