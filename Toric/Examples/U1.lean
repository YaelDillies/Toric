import Mathlib
import Toric.GroupScheme.Character

noncomputable section

open scoped Polynomial.Bivariate

open Polynomial TensorProduct

variable {R : Type*} [CommRing R]

variable (R) in
abbrev U1Ring : Type _ := R[X][Y] ⧸ Ideal.span {(X ^ 2 + Y ^ 2 - 1 : R[X][Y])}

abbrev U1Ring.mk (p : R[X][Y]) : (U1Ring R) := Ideal.Quotient.mk _ p

def Polynomial.aevalAEval {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] (x y : A) :
    R[X][Y] →ₐ[R] A where
  toFun p := eval x (eval₂ (mapRingHom (algebraMap R A)) (C y) p)
  map_one' := by sorry
  map_mul' := by sorry
  map_zero' := by sorry
  map_add' := by sorry
  commutes' := by sorry

instance : Algebra R (U1Ring R ⊗[R] U1Ring R) :=
  Algebra.TensorProduct.leftAlgebra (A := U1Ring R) (B := U1Ring R)

instance : CoalgebraStruct R (U1Ring R) where
  comul := (Ideal.Quotient.liftₐ _
    (aevalAEval (.mk X ⊗ₜ .mk X - .mk Y ⊗ₜ .mk Y) (.mk X ⊗ₜ .mk Y - .mk Y ⊗ₜ .mk X)) (by
    sorry
    )).toLinearMap
  counit := (Ideal.Quotient.liftₐ _ (aevalAEval 1 0) (by
    sorry
    )).toLinearMap

instance : Coalgebra R (U1Ring R) where
  coassoc := sorry
  rTensor_counit_comp_comul := sorry
  lTensor_counit_comp_comul := sorry

instance : Bialgebra R (U1Ring R) where
  counit_one := sorry
  mul_compr₂_counit := sorry
  comul_one := sorry
  mul_compr₂_comul := sorry

instance : HopfAlgebra R (U1Ring R) where
  antipode := (Ideal.Quotient.liftₐ _
    (aevalAEval (.mk X) (- .mk Y)) (by
    sorry
    )).toLinearMap
  mul_antipode_rTensor_comul := sorry
  mul_antipode_lTensor_comul := sorry
