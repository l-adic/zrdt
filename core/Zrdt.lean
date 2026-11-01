import Zrdt.Digest
import Zrdt.Sha256
import Zrdt.Record
import Zrdt.Encode
import Zrdt.Store
import Zrdt.RelStore
import Zrdt.Provenance
import Zrdt.Commit
import Zrdt.Serve
import Zrdt.ChatStore
import Zrdt.Proto
import Zrdt.Vectors

/-!
# Zrdt: the shipped code (no Mathlib)

Root module of the `zrdt-core` package. Each module is imported here as it lands
(docs/PLAN.md §3.1, phase B order: Digest → Sha256 → Record → Encode → Store → Provenance;
phase C: Commit, Proto, Vectors; docs/JOIN_PLAN.md phase 1: Serve). `Zrdt.Vectors` holds the
vectors and their `#guard`s; it has no `main` (`Zrdtd/Vectors.lean` prints them), so `zrdtd`
never links it.
-/
