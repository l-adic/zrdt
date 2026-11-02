/-
Copyright (c) 2026 zrdt contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: zrdt contributors
-/
import Zrdt.Torrent
import Zrdt.PieceProofs

/-!
# The apps, lane torrent: the bridge to the proofs package (docs/apps/BUILD_M1.md §C.2)

**Owner: lane torrent.** Every statement of lane torrent is proved about the shipped code in
`core/` with Init and Std only (`core/Zrdt/PieceProofs.lean`, namespaces `Zrdt.PieceProofs` and
`Zrdt.Torrent`), so none needs Mathlib or the spec model. `Crdt/Merkle/Api.lean` (Part 6b)
restates the advertised ones in the namespace `Zrdt.Apps` with the collision spelled out, and
`Test/Axioms.lean` pins them; this module only brings `core`'s torrent modules into the root
package for `Api.lean`.

A piece store is a `CheckedStore` like any chat, so the spec-level statements of Parts 1 to 3
(`fetched`, `agree`, ...) hold of it unchanged. A complete store's heads are `{F}`, whose digest
the announcement A already fixes, so `agree` adds nothing beyond `assemble_unique` (BUILD_M1 §A.1).
-/
