import Mathlib.CategoryTheory.Monoidal.CommGrp_
import Toric.Mathlib.CategoryTheory.Monoidal.Grp_

open CategoryTheory ChosenFiniteProducts MonoidalCategory Grp_Class Opposite

universe w v u

variable {C : Type u} [Category.{v} C] [ChosenFiniteProducts C]

class abbrev CommGrp_Class {C : Type*} [Category C] [ChosenFiniteProducts C] (X : C) :=
  Grp_Class X, IsCommMon X

instance (X : C) [CommGrp_Class X] : CommGrp_Class (Grp_.mk' X).X := ‹_›

section Yoneda
variable (X : C)

/-- If `X` represents a presheaf of groups, then `X` is a group object. -/
def CommGrp_Class.ofRepresentableBy (F : Cᵒᵖ ⥤ CommGrp.{w})
    (α : (F ⋙ forget _).RepresentableBy X) : CommGrp_Class X where
  __ := Grp_Class.ofRepresentableBy X (F ⋙ forget₂ CommGrp Grp) α
  __ := IsCommMon.ofRepresentableBy X (F ⋙ forget₂ CommGrp CommMonCat) α

end Yoneda

namespace CommGrp_

def mk' (X : C) [Grp_Class X] [IsCommMon X] : CommGrp_ C where
  __ := Grp_.mk' X
  mul_comm := IsCommMon.mul_comm X

instance (X : CommGrp_ C) : CommGrp_Class X.X where
  mul_comm' := X.mul_comm

end CommGrp_
