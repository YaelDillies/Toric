import Mathlib.Algebra.Module.Equiv.Defs

lemma LinearEquiv.toLinearMap_comp_symm_comp
    {R₁ R₂ R₃ : Type*} [Semiring R₁] [Semiring R₂] [Semiring R₃]
    {σ₂₃ : R₂ →+* R₃} {σ₃₂ : R₃ →+* R₂} {σ₁₂ : R₁ →+* R₂} {σ₁₃ : R₁ →+* R₃}
    [RingHomInvPair σ₂₃ σ₃₂] [RingHomInvPair σ₃₂ σ₂₃]
    [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] [RingHomCompTriple σ₁₃ σ₃₂ σ₁₂]
    {P M N : Type*} [AddCommMonoid P] [AddCommMonoid M] [AddCommMonoid N]
    [Module R₁ P] [Module R₂ M] [Module R₃ N] (e : M ≃ₛₗ[σ₂₃] N) (f : P →ₛₗ[σ₁₃] N) :
    e.toLinearMap ∘ₛₗ e.symm.toLinearMap ∘ₛₗ f = f :=
  (LinearEquiv.eq_toLinearMap_symm_comp (e.symm.toLinearMap ∘ₛₗ f) f).mp rfl

