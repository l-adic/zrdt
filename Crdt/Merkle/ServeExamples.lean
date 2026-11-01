/-
Copyright (c) 2026 zrdt contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: zrdt contributors
-/
import Mathlib
import Crdt.Merkle.ServeAbsRel

set_option linter.unusedSectionVars false

/-!
# `serve_after` and `serve_boundary` on real replies (docs/JOIN_PLAN.md §7.1)

`core/Zrdt/Serve.lean` proves `serve_after` and `serve_boundary` about `SERVE`'s reply, and checks
real replies with `#guard`; the kernel cannot run `serve` itself (its walk is well-founded
recursion). Here each theorem gets an input whose hypothesis holds, without running `serve`: the
bridge of `ServeAbs.lean` and `ServeAbsRel.lean` says, in the spec's words, exactly which entries
a catch-up reply has (`after_mem_serve`, `boundary_mem_serve`), and the kernel only computes
digests and audiences of small records.

* `Examples.reply_after`: Alice's message to herself, and Bob's reply to it, in a closed store.
  Alice asks for a catch-up: she may see her message, not Bob's reply (she holds no opening for
  it), so the reply goes to her as an `after` entry, structure without content.
* `Examples.reply_boundary`: Bob, a former newcomer, serves Carol from his relative store and holds
  no opening, so the reply carries no record; his head `a2` goes as a boundary digest.
-/

namespace Zrdt

open Crdt.Merkle

/-- Reaching from no digest reaches nothing. -/
theorem Examples.not_reach_empty' (s : SpecStore) (d : Digest) : ¬ Reach hashSpec s ∅ d :=
  fun h => by simpa using Reach.mem_of_bound hashSpec (R := ∅) subset_rfl (by simp) h

namespace Serve

namespace Examples

/-- Bob's reply to Alice's message to herself. Its commitment is a placeholder: Bob's opening is
not held by anyone here. -/
def replyToSelf : Rec := Rec.make Zrdt.Examples.group (Zrdt.Examples.dig 0xb9) #[selfDigest]
  Zrdt.Examples.bob

/-- The closed store with Alice's message and Bob's reply. -/
def selfStore2 : CheckedStore := (selfStore.accept replyToSelf).2

/-- Bob's reply links Alice's message (computed by the kernel). -/
theorem replyToSelf_links : replyToSelf.links = #[selfDigest] := by decide +kernel

/-- The reply's digest is not Alice's message's (computed by the kernel). -/
theorem replyToSelf_ne : hashRecord replyToSelf ≠ selfDigest := by decide +kernel

/-- `selfStore` is of the examples' chat and holds only Alice's message. -/
theorem selfStore_only : selfStore.raw.group = Zrdt.Examples.group ∧
    ∀ (k : Digest) (x : Rec), selfStore.raw.map[k]? = some x → x = selfMsg.1 := by
  show (rawAccept (CheckedStore.empty Zrdt.Examples.group).raw selfMsg.1).2.group = _ ∧
    ∀ (k : Digest) (x : Rec),
      (rawAccept (CheckedStore.empty Zrdt.Examples.group).raw selfMsg.1).2.map[k]? = some x →
      x = selfMsg.1
  cases hres : (rawAccept (CheckedStore.empty Zrdt.Examples.group).raw selfMsg.1).1 with
  | accepted d =>
    obtain ⟨-, hg, hmap, -⟩ := rawAccept_accepted (c' :=
      (rawAccept (CheckedStore.empty Zrdt.Examples.group).raw selfMsg.1).2) (Prod.ext hres rfl)
    refine ⟨hg, fun k x hk => ?_⟩
    rw [hmap, Std.ExtTreeMap.getElem?_insert] at hk
    split at hk
    · exact (Option.some.inj hk).symm
    · simp [CheckedStore.empty] at hk
  | _ =>
    have h := rawAccept_unchanged (c := (CheckedStore.empty Zrdt.Examples.group).raw)
      (r := selfMsg.1) (fun d h' => by rw [hres] at h'; cases h')
    rw [h]
    exact ⟨rfl, fun k x hk => by simp [CheckedStore.empty] at hk⟩

/-- Accepting Bob's reply into `selfStore` adds it under its digest. -/
theorem selfStore2_map :
    selfStore2.raw.map = selfStore.raw.map.insert (hashRecord replyToSelf) replyToSelf := by
  have hsm : selfStore.raw.map[selfDigest]? = some selfMsg.1 := selfStore_get
  obtain ⟨hgrp, hone⟩ := selfStore_only
  have hk : ∀ k, k ∈ selfStore.raw.map → k = selfDigest := by
    intro k hk
    obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp (Std.ExtTreeMap.mem_iff_isSome_getElem?.mp hk)
    have := hone k r hr
    subst this
    exact (selfStore.built.hash_eq k _ hr).symm
  have hnot : hashRecord replyToSelf ∉ selfStore.raw.map := fun h =>
    replyToSelf_ne (hk _ h)
  have hok : (rawAccept selfStore.raw replyToSelf).1 = .accepted (hashRecord replyToSelf) :=
    rawAccept_of_ok (by rw [hgrp]; rfl) (by simp [Rec.WellSized, replyToSelf_links, maxLinks])
      (by
        intro x hx
        rw [replyToSelf_links] at hx
        simp only [List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at hx
        subst hx
        exact Std.ExtTreeMap.mem_iff_isSome_getElem?.mpr (by simp [hsm]))
      (fun old ho => absurd (Std.ExtTreeMap.mem_iff_isSome_getElem?.mpr (by simp [ho])) hnot)
      (fun _ => by
        have : selfStore.raw.map.size ≤ 1 := by
          rw [← Std.ExtTreeMap.length_keys]
          have hsub : selfStore.raw.map.keys ⊆ [selfDigest] := fun k hk' =>
            List.mem_singleton.mpr (hk k (Std.ExtTreeMap.mem_keys.mp hk'))
          exact (Std.ExtTreeMap.nodup_keys.length_le_of_subset hsub).trans (by simp)
        simp [maxRecords]; omega)
  have h := rawAccept_accepted (c' := (rawAccept selfStore.raw replyToSelf).2) (Prod.ext hok rfl)
  exact h.2.2.1

/-- `selfStore2` holds Bob's reply under its digest. -/
theorem selfStore2_get_reply : selfStore2.get (hashRecord replyToSelf) = some replyToSelf := by
  show selfStore2.raw.map[hashRecord replyToSelf]? = some replyToSelf
  rw [selfStore2_map]
  exact Std.ExtTreeMap.getElem?_insert_self

/-- `selfStore2` still holds Alice's message. -/
theorem selfStore2_get_self : selfStore2.get selfDigest = some selfMsg.1 := by
  show selfStore2.raw.map[selfDigest]? = some selfMsg.1
  have hne : compare (hashRecord replyToSelf) selfDigest ≠ .eq := fun h =>
    replyToSelf_ne (Std.LawfulEqCmp.compare_eq_iff_eq.mp h)
  rw [selfStore2_map, Std.ExtTreeMap.getElem?_insert]
  simp only [hne, ↓reduceIte]
  exact selfStore_get

/-- Alice may see her message: its held opening seats her. -/
theorem self_entitled : entitledHere selfHeld (rq Zrdt.Examples.alice keyAlice) selfDigest
    selfMsg.1 = true := by
  obtain ⟨aud, ha, hs⟩ := selfMsg_seats
  simp [entitledHere, audienceFor, selfHeld, selfMsg_matches, ha, hs, rq]

/-- Alice is not seated in Bob's reply: she holds no opening and no audience for it. -/
theorem reply_not_entitled : entitledHere selfHeld (rq Zrdt.Examples.alice keyAlice)
    (hashRecord replyToSelf) replyToSelf = false := by
  have hne : compare selfDigest (hashRecord replyToSelf) ≠ .eq := fun h =>
    replyToSelf_ne (Std.LawfulEqCmp.compare_eq_iff_eq.mp h).symm
  simp [entitledHere, audienceFor, selfHeld, Std.ExtTreeMap.getD_insert, hne]

/-- **`serve_after`, on a real reply.** Bob's reply goes to Alice as an `after` entry. -/
theorem reply_after : Entry.after replyToSelf ∈
    serve selfStore2.raw selfMe selfHeld (rq Zrdt.Examples.alice keyAlice) := by
  have hq : (rq Zrdt.Examples.alice keyAlice).wanted = none := rfl
  have hsince : ∀ d, d ∉ sinceReach selfStore2.raw (rq Zrdt.Examples.alice keyAlice) := by
    intro d hd
    have := (mem_sinceReach (c := selfStore2)).mp hd
    simpa [rq] using Zrdt.Examples.not_reach_empty' _ _ this.2
  refine (after_mem_serve hq).mpr ⟨_, selfStore2_get_reply, ?_, ?_⟩
  · rintro ⟨h, -⟩
    rw [reply_not_entitled] at h
    cases h
  · refine (mem_upSet_of_get selfStore2_get_reply).mpr ((mem_servedF hashSpec).mpr ⟨?_, ?_⟩)
    · exact ((selfStore2.get_eq_some_iff).mp selfStore2_get_reply).1
    · refine ⟨toSpec selfMsg.1, ((selfStore2.get_eq_some_iff).mp selfStore2_get_self).1,
        (visSpec_of_get selfStore2_get_self).mpr ⟨self_entitled, hsince _⟩, ?_⟩
      rw [hashSpec_toSpec, hashSpec_toSpec]
      refine .link (r := toSpec replyToSelf)
        ((selfStore2.get_eq_some_iff).mp selfStore2_get_reply).1
        (by rw [hashSpec_toSpec]; exact .head (Finset.mem_singleton_self _))
        (mem_toSpec_links.mpr (by rw [replyToSelf_links]; simp [selfDigest]))

/-- `serve_after` applied to it: Bob's reply is stored and in the walk back from the records Alice
may see. -/
example : ∃ d : Digest, selfStore2.raw.map[d]? = some replyToSelf ∧
    d ∈ upSet selfStore2.raw selfHeld (rq Zrdt.Examples.alice keyAlice) :=
  serve_after reply_after

/-- `serve_after_reaches` applied to it: it reaches a record Alice may see. -/
example : toSpec replyToSelf ∈ abs selfStore2 ∧
    ∃ t ∈ abs selfStore2, visSpec selfStore2 selfHeld (rq Zrdt.Examples.alice keyAlice) t ∧
      Reach hashSpec (abs selfStore2) {hashRecord replyToSelf} (hashSpec t) :=
  serve_after_reaches reply_after

end Examples

namespace Rel.Examples

/-- `a2` is a head of Bob's relative store (computed by the kernel). -/
theorem bobRel_head_a2 : bobRel.raw.heads.contains (hashRecord Zrdt.Examples.a2) = true := by
  decide +kernel

/-- **`serve_boundary`, on a real reply from a relative store.** Bob holds no opening, so Carol's
catch-up from him carries no record, and his head `a2` goes as a boundary digest. -/
theorem reply_boundary : Entry.boundary (hashRecord Zrdt.Examples.a2) ∈
    serve bobRel.raw meBob ∅ (Serve.Examples.rq Zrdt.Examples.carol Serve.Examples.keyCarol) := by
  have hh : hashRecord Zrdt.Examples.a2 ∈ bobRel.raw.heads :=
    Std.ExtTreeSet.contains_iff_mem.mp bobRel_head_a2
  obtain ⟨hm, hnl⟩ := (bobRel.built.heads_iff _).mp hh
  refine (boundary_mem_serve rfl).mpr ⟨?_, ?_, .inr ?_⟩
  · by_cases hmap : hashRecord Zrdt.Examples.a2 ∈ bobRel.raw.map
    · exact .inl hmap
    · exact .inr (RelStore.mem_boundaryDigests.mpr ⟨hm.resolve_left hmap, hmap⟩)
  · intro hu
    obtain ⟨-, v, hv, -⟩ := mem_upSet.mp hu
    obtain ⟨r, -, he, -⟩ := mem_visList.mp hv
    simp [entitledHere, audienceFor] at he
  · intro hl
    obtain ⟨k, -, r, hr, hd⟩ := mem_linksOf_code.mp hl
    exact hnl k r hr hd

/-- `serve_boundary` applied to it: `a2` is a stored record outside the walk. -/
example : (∃ r, bobRel.raw.map[hashRecord Zrdt.Examples.a2]? = some r ∧
      hashRecord Zrdt.Examples.a2 ∉
        upSet bobRel.raw ∅ (Serve.Examples.rq Zrdt.Examples.carol Serve.Examples.keyCarol) ∧
      (entitledHere ∅ (Serve.Examples.rq Zrdt.Examples.carol Serve.Examples.keyCarol)
          (hashRecord Zrdt.Examples.a2) r = true →
        (Serve.Examples.rq Zrdt.Examples.carol Serve.Examples.keyCarol).wanted = none ∧
        (sinceReach bobRel.raw
          (Serve.Examples.rq Zrdt.Examples.carol Serve.Examples.keyCarol)).contains
          (hashRecord Zrdt.Examples.a2) = true)) ∨
    (meBob.boundary.contains (hashRecord Zrdt.Examples.a2) = true ∧
      bobRel.raw.map.contains (hashRecord Zrdt.Examples.a2) = false) :=
  serve_boundary reply_boundary

/-- `Rel.serve_boundary_spec` applied to it: from `a2`, no record Carol may see is reachable. -/
example : hashRecord Zrdt.Examples.a2 ∈ inView hashSpec bobRel.raw.abs (boundarySpec meBob) ∧
    ∀ t ∈ bobRel.raw.abs,
      visSpec bobRel ∅ (Serve.Examples.rq Zrdt.Examples.carol Serve.Examples.keyCarol) t →
      ¬ Reach hashSpec bobRel.raw.abs {hashRecord Zrdt.Examples.a2} (hashSpec t) :=
  serve_boundary_spec rfl reply_boundary

end Rel.Examples

end Serve

end Zrdt
