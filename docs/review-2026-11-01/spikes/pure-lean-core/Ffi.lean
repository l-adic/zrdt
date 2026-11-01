import ZCore.Store

namespace ZCore.Ffi

@[export zrdt_lean_sha256] def ffiSha256 (b : ByteArray) : ByteArray := (sha256 b).bytes
@[export zrdt_lean_store_new] def ffiNew (_ : Unit) : Store := {}
@[export zrdt_lean_accept] def ffiAccept (s : Store) (rec : ByteArray) : Store := s.accept rec
@[export zrdt_lean_size] def ffiSize (s : Store) : UInt32 := s.size.toUInt32
@[export zrdt_lean_digest_of] def ffiDigestOf (b : ByteArray) : Digest := sha256 b
@[export zrdt_lean_digestS_of] def ffiDigestSOf (b : ByteArray) : DigestS :=
  let d := sha256 b; ⟨d.bytes, d.size_eq⟩
@[export zrdt_lean_digest_bytes] def ffiDigestBytes (d : Digest) : ByteArray := d.bytes

end ZCore.Ffi
