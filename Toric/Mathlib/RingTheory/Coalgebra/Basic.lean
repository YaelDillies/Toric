import Mathlib.RingTheory.Coalgebra.Basic

open TensorProduct

variable {R A : Type*} [CommSemiring R]

namespace Coalgebra
variable [AddCommMonoid A] [Module R A] [Coalgebra R A]

variable (R A) in
/-- A coalgebra `A` is cocommutative if its comultiplication `δ : A → A ⊗ A` commutes with the
swapping `β : A ⊗ A ≃ A ⊗ A` of the factors in the tensor product. -/
class IsCocomm where
  protected comm_comp_comul : (TensorProduct.comm R A A).comp comul = comul

variable [IsCocomm R A]

variable (R A) in
@[simp] lemma comm_comp_comul : (TensorProduct.comm R A A).comp comul = comul :=
  IsCocomm.comm_comp_comul

variable (R) in
@[simp] lemma comm_comul (a : A) : TensorProduct.comm R A A (comul a) = comul a :=
  congr($(comm_comp_comul R A) a)

end Coalgebra
