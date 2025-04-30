import Mathlib.Algebra.Order.Nonneg.Module
import Mathlib.RingTheory.Finiteness.Basic

namespace Nonneg

section Ring

variable (𝕜 E : Type*) [Ring 𝕜] [LinearOrder 𝕜] [IsOrderedRing 𝕜] [AddCommMonoid E] [Module 𝕜 E]

/-- A linearly ordered ring is finitely generated as a module over the non-negative scalars. -/
instance isFiniteOver : Module.Finite {c : 𝕜 // 0 ≤ c} 𝕜 := by
  rw [Module.finite_def, Submodule.fg_def]
  refine ⟨{1, -1}, by simp, ?_⟩
  rw [Submodule.eq_top_iff']
  intro x
  by_cases hx : 0 ≤ x
  · have x_eq_smul : x = (⟨x, hx⟩ : {c : 𝕜 // 0 ≤ c}) • 1 := by simp
    rw [x_eq_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_insert 1 {-1}))
  · have x_eq_smul : x = (⟨-x, neg_nonneg.mpr (not_le.mp hx).le⟩ : {c : 𝕜 // 0 ≤ c}) • -1 := by simp
    rw [x_eq_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_insert_of_mem 1 rfl))

/-- If a module is finite over a linearly ordered ring, then it is also finite over the non-negative
scalars. -/
instance isFiniteModuleOver [h : Module.Finite 𝕜 E] : Module.Finite {c : 𝕜 // 0 ≤ c} E :=
  Module.Finite.trans 𝕜 E

end Ring

end Nonneg
