/-
Copyright (c) 2026 zrdt contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: zrdt contributors
-/
import Zrdt.Torrent
import Zrdt.PieceProofs

/-!
# The apps, lane torrent: proofs with Mathlib (docs/apps/BUILD_M1.md §C.2)

**Owner: lane torrent.** Proofs about torrent and piece stores that need the spec model (`abs`,
`fetched_agree`, the `RelStore` model) or `Zrdt.encode_injective`. Statements for which Init and Std
suffice live in `core/Zrdt/Torrent.lean` and `core/Zrdt/PieceProofs.lean`. `Crdt/Merkle/Api.lean`
imports this file and states lane torrent's advertised statements in its section `[lane torrent]` (a
proof that needs `CheckedStore.agree` or another statement of `Api.lean` goes there), so this file
must not import `Api.lean`. Add `import Mathlib` and the `Crdt.Merkle` modules you need.
Empty in the skeleton.
-/
