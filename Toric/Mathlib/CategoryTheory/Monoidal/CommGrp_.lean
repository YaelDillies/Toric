import Mathlib.CategoryTheory.Monoidal.CommGrp_
import Toric.Mathlib.CategoryTheory.Monoidal.Mon_

universe v₁ v₂ u₁ u₂ u
open CategoryTheory ChosenFiniteProducts MonoidalCategory Grp_Class Opposite

variable {C : Type*} [Category C]

namespace CommGrp_

variable [ChosenFiniteProducts C]

def mk' (X : C)  [Grp_Class X] [IsCommMon X] : CommGrp_ C where
  __ := Grp_.mk' X
  mul_comm := IsCommMon.mul_comm X

instance (X : CommGrp_ C) : IsCommMon X.X where
  mul_comm' := X.mul_comm

end CommGrp_
