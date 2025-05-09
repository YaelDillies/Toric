import Mathlib.CategoryTheory.Monoidal.CommGrp_
import Toric.Mathlib.CategoryTheory.Monoidal.Grp_

open CategoryTheory ChosenFiniteProducts MonoidalCategory Grp_Class Opposite

universe w v u

variable {C : Type u} [Category.{v} C] [ChosenFiniteProducts C] [BraidedCategory C]

class abbrev CommGrp_Class (X : C) := Grp_Class X, IsCommMon X

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

section GrpGrp

/-- The yoneda embedding of `CommGrp_C` into presheaves of groups. -/
@[simps]
def yonedaCommGrpGrpObj (X : CommGrp_ C) : (Grp_ C)ᵒᵖ ⥤ CommGrp where
  obj Y := .of (unop Y ⟶ X.toGrp_)
  map {Y Z} f := CommGrp.ofHom {
    toFun := (f.unop ≫ ·)
    map_one' := by ext; simp [Grp_.Hom.hom_one]
    map_mul' g h := by ext; simpa using ((yonedaGrpObj X.X).map f.unop.1.op).hom.map_mul g.hom h.hom
    }

/-- The yoneda embedding of `CommGrp_C` into presheaves of groups. -/
@[simps]
def yonedaCommGrpGrp : CommGrp_ C ⥤ (Grp_ C)ᵒᵖ ⥤ CommGrp where
  obj := yonedaCommGrpGrpObj
  map {X₁ X₂} ψ := {
    app Y := CommGrp.ofHom {
      toFun := (· ≫ ψ)
      map_one' := by ext; simp [Grp_.Hom.hom_one]
      map_mul' f g := by
        ext; simpa using ((yonedaGrp.map ψ).app (op (unop Y).X)).hom.map_mul f.hom g.hom
    }
    naturality {Y₁ Y₂} φ := by ext; simp
  }

end GrpGrp
end CommGrp_
