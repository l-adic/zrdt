import Zrdt.Digest
import Zrdt.Sha256
import Zrdt.Record
import Zrdt.Encode

/-!
# Zrdt: the shipped code (no Mathlib)

Root module of the `zrdt-core` package. Each module is imported here as it lands
(docs/PLAN.md §3.1, phase B order: Digest → Sha256 → Record → Encode → Store → Provenance;
phase C: Commit, Proto, Vectors).
-/
