import Mathlib.LinearAlgebra.TensorProduct.Associator

namespace TensorProduct
variable {R M M' N N' P P' : Type*} [CommSemiring R]
  [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P] [Module R M] [Module R N] [Module R P]
  [AddCommMonoid M'] [AddCommMonoid N'] [AddCommMonoid P'] [Module R M'] [Module R N'] [Module R P']

attribute [local ext] TensorProduct.ext

@[simp] lemma rightComm_comp_map_map (f : M →ₗ[R] M') (g : N →ₗ[R] N') (h : P →ₗ[R] P') :
    (rightComm R M' N' P').toLinearMap ∘ₗ map (map f g) h
      = map (map f h) g ∘ₗ (rightComm R M N P).toLinearMap := by ext; simp

lemma rightComm_def :
    rightComm R M N P =
      TensorProduct.assoc _ _ _ _ ≪≫ₗ
        congr (.refl _ _) (TensorProduct.comm _ _ _) ≪≫ₗ
        (TensorProduct.assoc _ _ _ _).symm := by apply LinearEquiv.toLinearMap_injective; ext; simp

end TensorProduct
