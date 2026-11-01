/-
Copyright (c) 2026 zrdt contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: zrdt contributors
-/
import Mathlib
import Crdt.Merkle.Defs

set_option linter.unusedSectionVars false

/-!
# Hash-linked records: integrity

The network and the peers a replica fetches from are not trusted. A replica only checks hashes
and links. This file proves what those checks buy.

* `fetched_agree` (headline): two replicas that fetched everything reachable from the same heads,
  and nothing else, hold the same store. Or two records in their stores have the same hash.
* `fetched_of_build`: a replica that accepts records one at a time is fetched from its own
  heads. Or two records in its store have the same hash. So the headline's hypotheses are met
  by honest replicas. `Chat.lean` restates it over `AcceptBuilt` as `fetched_build`.

Every theorem ends in `∨ CollisionIn hash u`, where `u` is the stores involved.
-/

namespace Crdt.Merkle

variable {α H K : Type*} [DecidableEq α] [DecidableEq H] [DecidableEq K]
variable (hash : Record α H K → H)
variable {s t : Store α H K} {hs : Finset H}

/-! ## Equal hashes -/

/-- Two records with the same hash are the same record, or they collide. -/
theorem accept_unique {a b : Record α H K} {d : H} (ha : hash a = d) (hb : hash b = d) :
    a = b ∨ CollisionIn hash {a, b} := by
  by_cases h : a = b
  · exact Or.inl h
  · exact Or.inr (CollisionIn.of_mem hash (Finset.mem_insert_self a {b})
      (Finset.mem_insert_of_mem (Finset.mem_singleton_self b)) h (ha.trans hb.symm))

/-- If every hash of `s` is a hash of `t`, then `s` is part of `t`. Or two records in `s ∪ t`
collide. -/
private theorem subset_of_digests_subset (h : digests hash s ⊆ digests hash t) :
    s ⊆ t ∨ CollisionIn hash (s ∪ t) := by
  by_cases hc : CollisionIn hash (s ∪ t)
  · exact Or.inr hc
  left
  intro r hr
  obtain ⟨r', hr', he⟩ := (mem_digests hash).mp (h ((mem_digests hash).mpr ⟨r, hr, rfl⟩))
  by_contra hrt
  exact hc (CollisionIn.of_mem hash (Finset.mem_union_right s hr') (Finset.mem_union_left t hr)
    (fun e ↦ hrt (e ▸ hr')) he)

/-- Stores with the same hashes are the same store. Or two records in `s ∪ t` collide. -/
theorem eq_of_digests_eq (h : digests hash s = digests hash t) :
    s = t ∨ CollisionIn hash (s ∪ t) := by
  rcases subset_of_digests_subset hash h.subset with h₁ | h₁
  · rcases subset_of_digests_subset hash h.symm.subset with h₂ | h₂
    · exact Or.inl (Finset.Subset.antisymm h₁ h₂)
    · exact Or.inr (by rwa [Finset.union_comm] at h₂)
  · exact Or.inr h₁

/-! ## Fetching from the same heads gives the same store -/

/-- If no two records in `s ∪ t` collide and `t` is complete for `hs`, then whatever you reach
from `hs` through `s` you also reach through `t`. -/
private theorem reach_mono_of_complete (hc : ¬ CollisionIn hash (s ∪ t)) (ht : Complete hash t hs) :
    ∀ d, Reach hash s hs d → Reach hash t hs d := by
  intro d hd
  induction hd with
  | head h => exact .head h
  | @link r d hr _ hl ih =>
    -- `t` holds a record with the hash of `r`; with no collision it is `r` itself.
    obtain ⟨r', hr', he⟩ := ht _ ih
    have : r' = r := by
      by_contra hne
      exact hc (CollisionIn.of_mem hash (Finset.mem_union_right s hr')
        (Finset.mem_union_left t hr) hne he)
    subst this
    exact .link hr' ih hl

/-- If no two records in `s ∪ t` collide, `t` is complete for `hs`, and `s` holds only records
reachable from `hs`, then `s` is part of `t`. -/
private theorem subset_of_fetched (hc : ¬ CollisionIn hash (s ∪ t)) (ht : Complete hash t hs)
    (hs' : Tight hash s hs) : s ⊆ t := by
  intro r hr
  obtain ⟨r', hr', he⟩ := ht _ (reach_mono_of_complete hash hc ht _ (hs' r hr))
  by_contra hrt
  exact hc (CollisionIn.of_mem hash (Finset.mem_union_right s hr') (Finset.mem_union_left t hr)
    (fun e ↦ hrt (e ▸ hr')) he)

/-- **Headline.** Two replicas that fetched the same heads, from sources they do not trust, hold
the same store. Or two records in their stores have the same hash. -/
theorem fetched_agree (hS : Fetched hash s hs) (hT : Fetched hash t hs) :
    s = t ∨ CollisionIn hash (s ∪ t) := by
  by_cases hc : CollisionIn hash (s ∪ t)
  · exact Or.inr hc
  · refine Or.inl (Finset.Subset.antisymm ?_ ?_)
    · exact subset_of_fetched hash hc hT.1 hS.2
    · exact subset_of_fetched hash (by rwa [Finset.union_comm]) hS.1 hT.2

/-! ## Honest replicas are fetched from their own heads -/

/-- Accepting one record keeps a closed store fetched from its own heads. Or two records in the
new store collide. -/
private theorem fetched_accept (hc : Closed hash s)
    (hf : Fetched hash s (heads hash s) ∨ CollisionIn hash s) (r : Record α H K) :
    Fetched hash (accept hash s r) (heads hash (accept hash s r)) ∨
      CollisionIn hash (accept hash s r) := by
  by_cases hl : r.links ⊆ digests hash s
  swap
  · rw [show accept hash s r = s by simp [accept, hl]]
    exact hf
  rw [accept_of_resolves hash hl]
  by_cases hr : r ∈ s
  · rw [Finset.insert_eq_of_mem hr]
    exact hf
  rcases hf with hf | hf
  swap
  · exact Or.inr (hf.mono hash (Finset.subset_insert r s))
  rcases heads_insert hash hc hr hl with hh | hh
  swap
  · exact Or.inr hh
  left
  have hci : Closed hash (insert r s) := by
    have := closed_accept hash hc r
    rwa [accept_of_resolves hash hl] at this
  refine ⟨complete_of_closed hash hci (heads_subset_digests hash _), ?_⟩
  rw [hh]
  intro x hx
  rcases Finset.mem_insert.mp hx with rfl | hx
  · exact .head (Finset.mem_insert_self _ _)
  -- An old record was reachable from the old heads. Each old head is still a head, or `r`
  -- links it.
  refine (hf.2 x hx).lift hash (Finset.subset_insert r s) (fun d hd ↦ ?_)
  by_cases hdl : d ∈ r.links
  · exact .link (Finset.mem_insert_self r s) (.head (Finset.mem_insert_self _ _)) hdl
  · exact .head (Finset.mem_insert_of_mem (Finset.mem_sdiff.mpr ⟨hd, hdl⟩))

/-- A store built by accepting records one at a time is fetched from its own heads. Or two
records in it have the same hash. -/
theorem fetched_of_build (l : List (Record α H K)) :
    Fetched hash (build hash l) (heads hash (build hash l)) ∨ CollisionIn hash (build hash l) := by
  have hempty : Fetched hash (∅ : Store α H K) (heads hash ∅) :=
    ⟨complete_of_closed hash (closed_empty hash) (heads_subset_digests hash ∅),
      fun r hr ↦ by simp at hr⟩
  unfold build
  suffices ∀ s, Closed hash s → (Fetched hash s (heads hash s) ∨ CollisionIn hash s) →
      Fetched hash (l.foldl (accept hash) s) (heads hash (l.foldl (accept hash) s)) ∨
        CollisionIn hash (l.foldl (accept hash) s) from
    this ∅ (closed_empty hash) (Or.inl hempty)
  induction l with
  | nil => exact fun s _ hf ↦ hf
  | cons r l ih =>
    intro s hc hf
    rw [List.foldl_cons]
    exact ih _ (closed_accept hash hc r) (fetched_accept hash hc hf r)

end Crdt.Merkle
