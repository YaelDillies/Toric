/-
Copyright (c) 2025 Justus Springer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justus Springer
-/
import Toric.Mathlib.Geometry.Convex.Cone.Dual
import Mathlib.LinearAlgebra.FiniteDimensional.Defs


namespace PointedCone

section CommRing

variable {R M N : Type*} [CommRing R] [PartialOrder R] [IsOrderedRing R] [AddCommGroup M]
  [AddCommGroup N] [Module R M] [Module R N] {p : M →ₗ[R] N →ₗ[R] R}

variable (p) in
def IsPolyhedral (c : PointedCone R N) : Prop :=
  ∃ t : Finset M, c = dual' p t

theorem IsPolyhedral.dual {t : Set M} (h : t.Finite) :
    IsPolyhedral p (dual' p t) := ⟨h.toFinset, by simp⟩

@[simp]
theorem IsPolyhedral.top : IsPolyhedral p (⊤ : PointedCone R N) := ⟨∅, by simp⟩

@[simp]
theorem IsPolyhedral.dual_dual_flip {c : PointedCone R N} (hc : IsPolyhedral p c) :
    dual' p (dual' p.flip (c : Set N)) = c := by
  obtain ⟨t,rfl⟩ := hc
  exact dual_dual_dual_eq_dual

end CommRing

section LinearOrderedField

variable {𝕜 M N : Type*} [Field 𝕜] [PartialOrder 𝕜] [IsOrderedRing 𝕜] [AddCommGroup M]
  [AddCommGroup N] [Module 𝕜 M] [Module 𝕜 N] {p : M →ₗ[𝕜] N →ₗ[𝕜] 𝕜}

/-- `⊥` is a polyhedral cone in a finite dimensional vector space over a linear
ordered field. -/
theorem IsPolyhedral.bot [hM : FiniteDimensional 𝕜 M] :
    IsPolyhedral p (⊥ : PointedCone 𝕜 N) := by
  classical
  obtain ⟨S,hS⟩ := Module.finite_def.mp hM
  let T : Finset M := S ∪ Finset.image (Neg.neg : M → M) S
  -- We first show that the span of R is closed under negation
  have neg_mem_span_R : ∀ x ∈ span 𝕜 R, (-x : E) ∈ span 𝕜 R := by
    apply Submodule.span_induction
    · intro x hx
      apply Submodule.subset_span
      -- Clearly, T is closed under negation. We show this by simple case distinction
      rw [Finset.mem_coe, Finset.mem_union] at hx
      cases' hx with hx₁ hx₂
      · apply Finset.mem_union_right
        simpa only [Finset.mem_map, Function.Embedding.coeFn_mk, neg_inj, exists_eq_right]
      · rw [Finset.mem_map, Function.Embedding.coeFn_mk] at hx₂
        obtain ⟨y,hy1,rfl⟩ := hx₂
        rw [neg_neg]
        exact Finset.mem_union_left _ hy1
    -- The three other cases in the induction are trivial
    · rw [neg_zero]
      exact Submodule.zero_mem _
    · intro x y _ _ hx hy
      rw [neg_add_rev]
      exact Submodule.add_mem _ hy hx
    · intro t x _ hx
      rw [←smul_neg]
      exact Submodule.smul_mem _ _ hx
  -- We now claim that `⊤` is generated as a pointed cone by `R`.
  use R
  symm
  rw [Submodule.eq_top_iff']
  rw [Submodule.eq_top_iff'] at hS
  intro x
  specialize hS x
  revert hS x
  -- By reverting x, the claim now says that every element of the span of S
  -- (as a usual `ℝ`-submodule) is contained in the span of `R` as a pointed cone.
  -- This can be shown by induction on the span.
  apply Submodule.span_induction
  · intro x hxS
    apply Submodule.subset_span
    exact Finset.mem_union_left _ hxS
  · apply Submodule.zero_mem
  · intro x y _ _ hx hy
    exact Submodule.add_mem _ hx hy
  · intro t x _ hx
    -- This is the only interesting case, as here we have split cases
    -- according to whether the scalar `t` is positive or not.
    by_cases ht : 0 ≤ t
    · exact Submodule.smul_mem _ ⟨t,ht⟩ hx
    · rw [←neg_neg (t • x), ←neg_smul, ←smul_neg]
      apply Submodule.smul_mem _ (⟨-t, by linarith⟩ : {a : 𝕜 // 0 ≤ a})
      -- We use our auxiliary statement from above
      exact neg_mem_span_R _ hx
end

end PointedCone

