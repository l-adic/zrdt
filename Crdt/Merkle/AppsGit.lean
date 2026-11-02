/-
Copyright (c) 2026 zrdt contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: zrdt contributors
-/
import Zrdt.Git

/-!
# The apps, lane git: proofs with Mathlib (docs/apps/BUILD_M1.md §C.3)

**Owner: lane git.** Proofs about git that need the spec model (`abs`, `fetched_agree`, the
`RelStore` model) or `Zrdt.encode_injective`. Statements for which Init and Std suffice live in
`core/Zrdt/Git.lean`. `Crdt/Merkle/Api.lean` imports this file and states lane git's advertised
statements in its section `[lane git]` (a proof that needs `CheckedStore.agree` or another statement
of `Api.lean` goes there), so this file must not import `Api.lean`. Add `import Mathlib` and the
`Crdt.Merkle` modules you need. Empty in the skeleton.
-/
