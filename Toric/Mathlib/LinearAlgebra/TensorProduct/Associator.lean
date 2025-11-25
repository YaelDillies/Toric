import Mathlib.LinearAlgebra.TensorProduct.Associator

namespace TensorProduct
variable {R M M' N N' P P' : Type*} [CommSemiring R]
  [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P] [Module R M] [Module R N] [Module R P]
  [AddCommMonoid M'] [AddCommMonoid N'] [AddCommMonoid P'] [Module R M'] [Module R N'] [Module R P']

attribute [local ext] TensorProduct.ext

@[simp] lemma rightComm_comp_map_map (f : M →ₗ[R] M') (g : N →ₗ[R] N') (h : P →ₗ[R] P') :
    (rightComm R M' N' P').toLinearMap ∘ₗ map (map f g) h
      = map (map f h) g ∘ₗ (rightComm R M N P).toLinearMap := by ext; simp

end TensorProduct
