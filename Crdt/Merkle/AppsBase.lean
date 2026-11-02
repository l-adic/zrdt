/-
Copyright (c) 2026 zrdt contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: zrdt contributors
-/
import Zrdt.Apps

/-!
# The apps, lane base: proofs with Mathlib (docs/apps/BUILD_M1.md §C.1)

**Owner: lane base.** Proofs about the apps' shared base (app messages, ids, encodings, the
dispatcher's guard) that need the spec model (`abs`, `fetched_agree`, the `RelStore` model) or
`Zrdt.encode_injective`. Statements for which Init and Std suffice live in `core/Zrdt/AppBase.lean`
and `core/Zrdt/Apps.lean`. `Crdt/Merkle/Api.lean` imports this file and states lane base's
advertised statements in its section `[lane base]` (a proof that needs `CheckedStore.agree` or
another statement of `Api.lean` goes there), so this file must not import `Api.lean`. Add `import
Mathlib` and the `Crdt.Merkle` modules you need. Empty in the skeleton.
-/
