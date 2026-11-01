/-
Copyright (c) 2026 zrdt contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: zrdt contributors
-/
import Mathlib
import Crdt.Merkle.Chat

set_option linter.unusedSectionVars false

/-!
# Salvage in the model, from the other side (for `open_iff` and `salvage_spec`)

`Chat.lean` shows that `buildRetry hash u` is accept-built and holds every accept-built part of
`u` (`salvage_built`, `salvage_maximal`). This file adds the matching bound from above:
`buildRetry hash u` is inside every store `E` that **takes in `u`**, that is, holds every record
of `u` whose links are all digests of records of `E`.

The code's loader (`acceptAll` on an empty store) gives such a store
(`Zrdt.CheckedStore.acceptAll_closed`, in `EncodeProofs.lean`). So:

- `buildRetry_eq_of_takesIn`: an accept-built part of `u` that takes in `u` is exactly
  `buildRetry hash u`. This is the core of `salvage_spec`.
- `subset_of_takesIn`: an accept-built `u` is inside every store that takes it in. This is the
  core of the "if" direction of `open_iff`: `acceptAll` then stores every record, so nothing is
  left over and `open` succeeds.
-/

namespace Crdt.Merkle

variable {α H K : Type*} [DecidableEq α] [DecidableEq H] [DecidableEq K]
variable (hash : Record α H K → H)

/-- Every round of salvage stays inside a store `E` that takes in `u`. -/
theorem retryRounds_subset_of_takesIn {u E : Store α H K}
    (hE : ∀ r ∈ u, r.links ⊆ digests hash E → r ∈ E) (n : ℕ) : retryRounds hash u n ⊆ E := by
  induction n with
  | zero => simp [retryRounds]
  | succ n ih =>
    intro r hr
    simp only [retryRounds, retryStep, Finset.mem_union, Finset.mem_filter] at hr
    rcases hr with hr | ⟨hru, hl⟩
    · exact ih hr
    · exact hE r hru (hl.trans (digests_mono hash ih))

/-- **Salvage is inside every store that takes in `u`.** If `E` holds every record of `u` whose
links are all digests of records of `E`, then `E` holds all of `buildRetry hash u`. -/
theorem buildRetry_subset_of_takesIn {u E : Store α H K}
    (hE : ∀ r ∈ u, r.links ⊆ digests hash E → r ∈ E) : buildRetry hash u ⊆ E :=
  retryRounds_subset_of_takesIn hash hE _

-- A set always takes itself in, so salvage stays inside it.
example : buildRetry Toy.hash {Toy.r0, Toy.r1, Toy.r2} ⊆ {Toy.r0, Toy.r1, Toy.r2} :=
  buildRetry_subset_of_takesIn Toy.hash (by decide)

/-- **Salvage, characterised.** A part `E` of `u` that is accept-built and takes in `u` is exactly
what salvage keeps. -/
theorem buildRetry_eq_of_takesIn {u E : Store α H K} (hsub : E ⊆ u) (hb : AcceptBuilt hash E)
    (hE : ∀ r ∈ u, r.links ⊆ digests hash E → r ∈ E) : buildRetry hash u = E :=
  (buildRetry_subset_of_takesIn hash hE).antisymm (salvage_maximal hash hb hsub)

-- Salvage of `{r0, r2, c5, c6}` (`r2` links `r1`, which is absent; `c5` and `c6` link each other)
-- keeps exactly `{r0}`: it is accept-built and takes in the rest.
example : buildRetry Toy.hash {Toy.r0, Toy.r2, Toy.c5, Toy.c6} = {Toy.r0} :=
  buildRetry_eq_of_takesIn Toy.hash (by decide) ⟨[Toy.r0], by decide, by decide⟩ (by decide)

/-- **An accept-built set is inside every store that takes it in.** -/
theorem subset_of_takesIn {u E : Store α H K} (hu : AcceptBuilt hash u)
    (hE : ∀ r ∈ u, r.links ⊆ digests hash E → r ∈ E) : u ⊆ E :=
  (salvage_maximal hash hu subset_rfl).trans (buildRetry_subset_of_takesIn hash hE)

example : ({Toy.r0, Toy.r1} : Store ℕ ℕ Unit) ⊆ {Toy.r0, Toy.r1, Toy.r2} :=
  subset_of_takesIn Toy.hash ⟨[Toy.r0, Toy.r1], by decide, by decide⟩ (by decide)

-- The hypothesis matters: the empty store does not take in `{r0}` (`r0` has no links, so it
-- would have to hold it), and `{r0}` is not inside it.
example : ¬ (∀ r ∈ ({Toy.r0} : Store ℕ ℕ Unit), r.links ⊆ digests Toy.hash ∅ →
    r ∈ (∅ : Store ℕ ℕ Unit)) := by
  decide

end Crdt.Merkle
