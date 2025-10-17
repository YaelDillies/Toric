import Mathlib.CategoryTheory.Monoidal.Cartesian.CommGrp_
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import Toric.Mathlib.CategoryTheory.Monoidal.Cartesian.Grp_

open CategoryTheory GrpObj Opposite
open scoped MonObj

universe v u

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] [BraidedCategory C]

namespace CommGrp

-- TODO: Make `CommGrp.toGrp` an abbrev in mathlib.
set_option allowUnsafeReducibility true in
attribute [reducible] CommGrp.toGrp

/-- The yoneda embedding of `CommGrp_C` into presheaves of groups. -/
@[simps]
def yonedaCommGrpGrpObj (G : CommGrp C) : (Grp C)ᵒᵖ ⥤ CommGrpCat where
  obj H := .of (unop H ⟶ G.toGrp)
  map {H I} f := CommGrpCat.ofHom {
    toFun := (f.unop ≫ ·)
    map_one' := by ext; simp [Mon.Hom.hom_one]
    map_mul' g h := by ext; simpa using ((yonedaGrpObj G.X).map f.unop.1.op).hom.map_mul g.hom h.hom
  }

/-- The yoneda embedding of `CommGrp_C` into presheaves of groups. -/
@[simps]
def yonedaCommGrpGrp : CommGrp C ⥤ (Grp C)ᵒᵖ ⥤ CommGrpCat where
  obj := yonedaCommGrpGrpObj
  map {X₁ X₂} ψ := {
    app Y := CommGrpCat.ofHom {
      toFun := (· ≫ ψ)
      map_one' := by ext; simp
      map_mul' f g := by
        ext; simpa using ((yonedaGrp.map ψ).app (op (unop Y).X)).hom.map_mul f.hom g.hom
    }
  }

end CommGrp
