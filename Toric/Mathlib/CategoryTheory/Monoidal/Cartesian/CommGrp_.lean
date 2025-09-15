import Mathlib.CategoryTheory.Monoidal.Cartesian.CommGrp_
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import Toric.Mathlib.CategoryTheory.Monoidal.Cartesian.Grp_

open CategoryTheory GrpObj Opposite
open scoped MonObj

universe v u

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] [BraidedCategory C]

namespace CommGrp_

-- TODO: Make `CommGrp_.toGrp_` an abbrev in mathlib.
set_option allowUnsafeReducibility true in
attribute [reducible] CommGrp_.toGrp_

/-- The yoneda embedding of `CommGrp_C` into presheaves of groups. -/
@[simps]
def yonedaCommGrpGrpObj (G : CommGrp_ C) : (Grp_ C)ᵒᵖ ⥤ CommGrp where
  obj H := .of (unop H ⟶ G.toGrp_)
  map {H I} f := CommGrp.ofHom {
    toFun := (f.unop ≫ ·)
    map_one' := by ext; simp [Mon_.Hom.hom_one]
    map_mul' g h := by ext; simpa using ((yonedaGrpObj G.X).map f.unop.1.op).hom.map_mul g.hom h.hom
  }

/-- The yoneda embedding of `CommGrp_C` into presheaves of groups. -/
@[simps]
def yonedaCommGrpGrp : CommGrp_ C ⥤ (Grp_ C)ᵒᵖ ⥤ CommGrp where
  obj := yonedaCommGrpGrpObj
  map {X₁ X₂} ψ := {
    app Y := CommGrp.ofHom {
      toFun := (· ≫ ψ)
      map_one' := by ext; simp
      map_mul' f g := by
        ext; simpa using ((yonedaGrp.map ψ).app (op (unop Y).X)).hom.map_mul f.hom g.hom
    }
    naturality {Y₁ Y₂} φ := by ext; simp
  }

end CommGrp_
