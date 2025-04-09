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

namespace LinearMap

variable {N}

variable (g : P →ₗ[R] Q) (f : N →ₗ[R] P)

-- Not sure if this should actually go into mathlib?
theorem lTensor_tensor :  lTensor (M ⊗[R] N) g  ∘ₗ (TensorProduct.assoc R M N P).symm =
    (TensorProduct.assoc R M N Q).symm ∘ₗ lTensor M (lTensor N g) :=
  TensorProduct.ext <| LinearMap.ext fun _ ↦ TensorProduct.ext rfl


theorem lTensor_tensor2 :  (TensorProduct.assoc R M N Q) ∘ₗ lTensor (M ⊗[R] N) g =
    lTensor M (lTensor N g) ∘ₗ (TensorProduct.assoc R M N P) :=
  by exact TensorProduct.ext_threefold fun x y ↦ congrFun rfl

end LinearMap
