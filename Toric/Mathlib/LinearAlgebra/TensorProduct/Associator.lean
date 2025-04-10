import Mathlib.LinearAlgebra.TensorProduct.Associator

suppress_compilation

variable {R : Type*} [CommSemiring R]
variable {R' : Type*} [Monoid R']
variable {R'' : Type*} [Semiring R'']
variable {A M N P Q S T : Type*}
variable [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P]
variable [AddCommMonoid Q] [AddCommMonoid S] [AddCommMonoid T]
variable [Module R M] [Module R N] [Module R Q] [Module R S] [Module R T]
variable [DistribMulAction R' M]
variable [Module R'' M]
variable (M N)

open scoped TensorProduct

variable [Module R P]

lemma TensorProduct.tensorTensorTensorComm_def
    {R : Type*} [CommSemiring R] (M N P Q : Type*)
    [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P] [AddCommMonoid Q]
    [Module R M] [Module R N] [Module R P] [Module R Q] :
    TensorProduct.tensorTensorTensorComm R M N P Q =
    (TensorProduct.assoc R M N (P ⊗[R] Q)).trans
      ((TensorProduct.congr (LinearEquiv.refl R M) (TensorProduct.leftComm R N P Q)).trans
        (TensorProduct.assoc R M P (N ⊗[R] Q)).symm) := rfl

@[simp]
lemma TensorProduct.coe_congr
    {R : Type*} [CommSemiring R] {M N P Q : Type*}
    [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P] [AddCommMonoid Q]
    [Module R M] [Module R N] [Module R P] [Module R Q]
    (f : M ≃ₗ[R] P) (g : N ≃ₗ[R] Q) :
    (TensorProduct.congr f g).toLinearMap = TensorProduct.map f g := rfl

lemma TensorProduct.leftComm_def
    {R : Type*} [CommSemiring R] (M N P : Type*)
    [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P]
    [Module R M] [Module R N] [Module R P] :
    TensorProduct.leftComm R M N P =
    (TensorProduct.assoc R M N P).symm.trans
      ((TensorProduct.congr (TensorProduct.comm R M N) (LinearEquiv.refl R P)).trans
        (TensorProduct.assoc R N M P)) := rfl

lemma LinearMap.lTensor_tensor
    {R : Type*} [CommSemiring R] (M N P Q : Type*)
    [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P] [AddCommMonoid Q]
    [Module R M] [Module R N] [Module R P] [Module R Q] (f : P →ₗ[R] Q) :
    LinearMap.lTensor (M ⊗[R] N) f =
      (TensorProduct.assoc R M N Q).symm ∘ₗ
        LinearMap.lTensor M (LinearMap.lTensor N f) ∘ₗ
          TensorProduct.assoc R M N P :=
  TensorProduct.ext <| TensorProduct.ext rfl

lemma LinearEquiv.toLinearMap_comp_symm_comp
    {R₁ R₂ R₃ : Type*} [Semiring R₁] [Semiring R₂] [Semiring R₃]
    {σ₂₃ : R₂ →+* R₃} {σ₃₂ : R₃ →+* R₂} {σ₁₂ : R₁ →+* R₂} {σ₁₃ : R₁ →+* R₃}
    [RingHomInvPair σ₂₃ σ₃₂] [RingHomInvPair σ₃₂ σ₂₃]
    [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] [RingHomCompTriple σ₁₃ σ₃₂ σ₁₂]
    {P M N : Type*} [AddCommMonoid P] [AddCommMonoid M] [AddCommMonoid N]
    [Module R₁ P] [Module R₂ M] [Module R₃ N] (e : M ≃ₛₗ[σ₂₃] N) (f : P →ₛₗ[σ₁₃] N) :
    e.toLinearMap ∘ₛₗ e.symm.toLinearMap ∘ₛₗ f = f :=
  (LinearEquiv.eq_toLinearMap_symm_comp (e.symm.toLinearMap ∘ₛₗ f) f).mp rfl
