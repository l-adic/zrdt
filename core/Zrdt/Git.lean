import Zrdt.AppBase

/-!
# Git (docs/apps/BUILD_M1.md §B.7, §C.3)

**Owner: lane git.** Ops `0x28`-`0x2F`: `GIT_PREPARE` `0x28`, `GIT_OBJECTS` `0x29`, `GIT_VIEW`
`0x2A`; `0x2B`-`0x2F` reserved. The git ops only read the daemon's state (`run` returns no new
state): a push's piece store is created and filled by lane base's ops, after the push record is
accepted into the channel.

The skeleton has no op yet: `parse` answers `none`, so `Zrdt.Apps` replies `UNKNOWN_OP`.
Lane git fills in this file (raw objects and `checkObjects`, the push body `"zgit1"`, the table,
the root rule, freshness, the gate, shares, the push log and the register, theorems), its op
names in `Proto.lean` (section `lane git`), its sessions in `Vectors.lean` (sections `lane
git`), its block in `Test/Axioms.lean`, and its part of `Crdt/Merkle/Api.lean` with proofs in
`Crdt/Merkle/AppsGit.lean`.
-/

namespace Zrdt.Git

open AppBase

/-- A git request. -/
inductive Request : Type

/-- A git reply. -/
inductive Reply : Type

/-- The request's payload (op byte first). -/
def Request.write : Request → ByteArray := nofun

/-- The reply's payload (status byte first). -/
def Reply.write : Reply → ByteArray := nofun

/-- The body parser of git op `op` (`0x28`-`0x2F`); `none`: not a git op. -/
def parse (_op : UInt8) : Option (Proto.Parser Request) := none

/-- Answer a git request. Read-only: the state does not change. -/
def run (_s : State) : Request → Reply := nofun

end Zrdt.Git
