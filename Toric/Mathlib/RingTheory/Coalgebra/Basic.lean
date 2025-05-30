import Mathlib.RingTheory.Coalgebra.Basic

open TensorProduct

variable {ι R A : Type*} [CommSemiring R] [AddCommMonoid A] [Module R A] [Coalgebra R A]

namespace Coalgebra

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

open Coalgebra

namespace Finsupp

instance instIsCocomm [IsCocomm R A] : IsCocomm R (ι →₀ A) where
  comm_comp_comul := by
    ext i : 1
    simp [comul_comp_lsingle, LinearMap.comp_assoc]
    simp [← LinearMap.comp_assoc, ← TensorProduct.map_comp_comm_eq]
    simp [LinearMap.comp_assoc]

end Finsupp
