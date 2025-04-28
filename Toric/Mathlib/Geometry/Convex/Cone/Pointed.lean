import Mathlib.Geometry.Convex.Cone.Pointed
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

variable {R E : Type*} [Semiring R] [PartialOrder R] [IsOrderedRing R] [AddCommGroup E]
  [Module R E] (s : Set E)


theorem span_nonneg_subset_span (s : Set E) :
    (Submodule.span {c : R // 0 ≤ c} s : Set E) ⊆ Submodule.span R s := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span hx
  | zero => exact zero_mem (Submodule.span R s)
  | add x y hx1 hy1 hx2 hy2 => exact Submodule.add_mem _ hx2 hy2
  | smul t x hx1 hx2 =>
    rw [Nonneg.mk_smul]
    exact Submodule.smul_mem _ _ hx2

theorem span_eq_nonneg_span_union_neg : (Submodule.span R s : Set E) =
    Submodule.span {c : R // 0 ≤ c} (s ∪ -s) := by
  apply le_antisymm
  · sorry
  · sorry


section LinearOrderedField

variable {𝕜 E : Type*} [Field 𝕜] [PartialOrder 𝕜] [IsOrderedRing 𝕜] [AddCommGroup E]
  [Module 𝕜 E]

local notation3 "𝕜≥0" => {c : 𝕜 // 0 ≤ c}

#check Submodule.fg_def
theorem PointedCone.fg [hE : FiniteDimensional 𝕜 E] (c : PointedCone 𝕜 E) : c.FG := by
  classical
  obtain ⟨S,hS⟩ := Module.finite_def.mp hE
  rw [Submodule.fg_def]
  use S ∪ -S
  split_ands
  · simp only [Set.involutiveNeg, Set.finite_union, Finset.finite_toSet, Set.finite_neg, and_self]
  · sorry

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

end LinearOrderedField


