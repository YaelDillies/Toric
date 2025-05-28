import Mathlib.LinearAlgebra.TensorProduct.Tower

namespace TensorProduct.AlgebraTensorModule

universe uR uA uB uM uN uP uQ uP' uQ'
variable {R : Type uR} {A : Type uA} {B : Type uB}
variable {M : Type uM} {N : Type uN} {P : Type uP} {Q : Type uQ} {P' : Type uP'} {Q' : Type uQ'}

variable [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]
variable [AddCommMonoid M] [Module R M] [Module A M]
variable [IsScalarTower R A M]
variable [AddCommMonoid N] [Module R N]
variable [AddCommMonoid P] [Module R P] [Module A P]
variable [IsScalarTower R A P]
variable [AddCommMonoid Q] [Module R Q]
variable [AddCommMonoid P'] [Module R P'] [Module A P'] [Module B P']
variable [IsScalarTower R A P'] [IsScalarTower R B P'] [SMulCommClass A B P']
variable [AddCommMonoid Q'] [Module R Q']

variable [Module B P] [IsScalarTower R B P] [SMulCommClass A B P]

lemma map_eq_map (f : M →ₗ[R] P) (g : N →ₗ[R] Q) : map f g = TensorProduct.map f g := rfl

lemma congr_eq_congr (f : M ≃ₗ[R] P) (g : N ≃ₗ[R] Q) : congr f g = TensorProduct.congr f g := by
  sorry

lemma assoc_eq_assoc  :
    assoc R R R M N P = TensorProduct.assoc R M N P := by
  sorry

lemma tensorTensorTensorComm_eq_tensorTensorTensorComm :
    tensorTensorTensorComm R R M N P Q = TensorProduct.tensorTensorTensorComm R M N P Q := by
  sorry

end TensorProduct.AlgebraTensorModule
