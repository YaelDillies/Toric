import Mathlib.LinearAlgebra.TensorProduct.Associator

open scoped TensorProduct

local notation "α" => TensorProduct.assoc

lemma LinearMap.lTensor_tensor
    {R : Type*} [CommSemiring R] (M N P Q : Type*)
    [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P] [AddCommMonoid Q]
    [Module R M] [Module R N] [Module R P] [Module R Q] (f : P →ₗ[R] Q) :
    LinearMap.lTensor (M ⊗[R] N) f = (α R M N Q).symm ∘ₗ (f.lTensor N).lTensor M ∘ₗ α R M N P :=
  TensorProduct.ext <| TensorProduct.ext rfl
