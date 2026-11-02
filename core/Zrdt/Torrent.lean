import Zrdt.AppBase

/-!
# Torrent (docs/apps/BUILD_M1.md §B.6, §C.2)

**Owner: lane torrent.** Ops `0x20`-`0x27`: `BT_BUILD` `0x20`, `BT_FILE` `0x21`; `0x22`-`0x27`
reserved. The torrent ops only read the daemon's state (`run` returns no new state): every piece
store is created and filled by lane base's ops (`PIECES_BIND`, `PIECE_ACCEPT`,
`PIECES_COMPLETE`).

The skeleton has no op yet: `parse` answers `none`, so `Zrdt.Apps` replies `UNKNOWN_OP`.
Lane torrent fills in this file (requests, replies, parser, writer, runner, `safeComponent`, the
manifest `"zbtF1"`, theorems), its op names in `Proto.lean` (section `lane torrent`), its sessions
in `Vectors.lean` (sections `lane torrent`), its block in `Test/Axioms.lean`, and its part of
`Crdt/Merkle/Api.lean` with proofs in `Crdt/Merkle/AppsTorrent.lean`.
-/

namespace Zrdt.Torrent

open AppBase

/-- A torrent request. -/
inductive Request : Type

/-- A torrent reply. -/
inductive Reply : Type

/-- The request's payload (op byte first). -/
def Request.write : Request → ByteArray := nofun

/-- The reply's payload (status byte first). -/
def Reply.write : Reply → ByteArray := nofun

/-- The body parser of torrent op `op` (`0x20`-`0x27`); `none`: not a torrent op. -/
def parse (_op : UInt8) : Option (Proto.Parser Request) := none

/-- Answer a torrent request. Read-only: the state does not change. -/
def run (_s : State) : Request → Reply := nofun

end Zrdt.Torrent
