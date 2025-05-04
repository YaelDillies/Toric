import Mathlib.LinearAlgebra.TensorProduct.Basic

variable {R M M₁ M₂ M₃ N N₁ N₂ N₃ : Type*} [CommSemiring R]
  [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
  [AddCommMonoid M₁] [Module R M₁] [AddCommMonoid N₁] [Module R N₁]
  [AddCommMonoid M₂] [Module R M₂] [AddCommMonoid N₂] [Module R N₂]
  [AddCommMonoid M₃] [Module R M₃] [AddCommMonoid N₃] [Module R N₃]

namespace TensorProduct

@[simp]
lemma coe_congr
    {R : Type*} [CommSemiring R] {M N P Q : Type*}
    [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P] [AddCommMonoid Q]
    [Module R M] [Module R N] [Module R P] [Module R Q]
    (f : M ≃ₗ[R] P) (g : N ≃ₗ[R] Q) :
    (TensorProduct.congr f g).toLinearMap = TensorProduct.map f g := rfl

lemma map_map (f₂ : M₂ →ₗ[R] M₃) (g₂ : N₂ →ₗ[R] N₃) (f₁ : M₁ →ₗ[R] M₂) (g₁ : N₁ →ₗ[R] N₂)
    (x : M₁ ⊗ N₁) : map f₂ g₂ (map f₁ g₁ x) = map (f₂ ∘ₗ f₁) (g₂ ∘ₗ g₁) x :=
  DFunLike.congr_fun (map_comp ..).symm x

end TensorProduct
