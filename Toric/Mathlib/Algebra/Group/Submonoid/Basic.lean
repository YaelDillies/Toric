import Mathlib.Algebra.Group.Submonoid.Basic

variable {M : Type*} [Monoid M] {s t : Set M}

namespace Submonoid

@[to_additive (attr := simp)]
lemma closure_sdiff_eq_closure (hts : t ⊆ closure (s \ t)) : closure (s \ t) = closure s := by
  refine (closure_mono Set.diff_subset).antisymm <| closure_le.mpr <| fun x hxs ↦ ?_
  by_cases hxt : x ∈ t
  · exact hts hxt
  · rw [SetLike.mem_coe, Submonoid.mem_closure]
    exact fun N hN ↦ hN <| Set.mem_diff_of_mem hxs hxt

@[to_additive (attr := simp)]
lemma closure_sdiff_singleton_one (s : Set M) : closure (s \ {1}) = closure s :=
  closure_sdiff_eq_closure <| by simp [one_mem]

end Submonoid
