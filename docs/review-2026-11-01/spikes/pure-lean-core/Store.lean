import Std.Data.HashMap
import ZCore.Digest

namespace ZCore

structure Store where
  map : Std.HashMap Digest ByteArray := {}

def Store.accept (s : Store) (rec : ByteArray) : Store :=
  { map := s.map.insert (sha256 rec) rec }

def Store.size (s : Store) : Nat := s.map.size

end ZCore
