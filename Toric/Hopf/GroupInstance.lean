import Mathlib
import Toric.Mathlib.CategoryTheory.ChosenFiniteProducts.Over

open CategoryTheory AlgebraicGeometry

attribute [local instance] ChosenFiniteProducts.ofFiniteProducts

variable {R : CommRingCat} {A : Under R} [HopfAlgebra R A]

instance : Grp_Class <| Over.mk <| Spec.map <| A.hom := sorry
  /- one := Over.homMk _ _
  mul := _
  one_mul' := _
  mul_one' := _
  mul_assoc' := _
  inv := _
  left_inv' := _
  right_inv' := _ -/
