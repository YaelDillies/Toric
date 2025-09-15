import Mathlib.CategoryTheory.Monoidal.Mon_

open CategoryTheory MonoidalCategory

assert_not_exists CartesianMonoidalCategory

/-! ### `mapMon` is braided -/

namespace CategoryTheory.Functor

variable {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D] {M X : C}
  [MonObj M] {F : C ⥤ D}

open LaxMonoidal OplaxMonoidal

open scoped Obj

attribute [local simp] ε_tensorHom_comp_μ_assoc in
instance [F.LaxMonoidal] : IsMon_Hom (ε F) where

section BraidedCategory
variable [BraidedCategory C] [BraidedCategory D] (F)

attribute [-simp] IsMon_Hom.one_hom_assoc in
attribute [local simp] tensorμ_comp_μ_tensorHom_μ_comp_μ_assoc MonObj.tensorObj.one_def
  MonObj.tensorObj.mul_def in
instance [F.LaxBraided] (M N : C) [MonObj M] [MonObj N] : IsMon_Hom («μ» F M N) where
  one_hom := by simp [← Functor.map_comp, leftUnitor_inv_comp_tensorHom_assoc]

attribute [-simp] IsMon_Hom.one_hom IsMon_Hom.one_hom_assoc IsMon_Hom.mul_hom in
attribute [local simp] ε_tensorHom_comp_μ_assoc tensorμ_comp_μ_tensorHom_μ_comp_μ_assoc
  MonObj.tensorObj.one_def MonObj.tensorObj.mul_def in
instance [F.LaxBraided] : F.mapMon.LaxMonoidal where
  ε := .mk (ε F)
  μ M N := .mk («μ» F M.X N.X)

attribute [-simp] IsMon_Hom.one_hom IsMon_Hom.one_hom_assoc IsMon_Hom.mul_hom in
attribute [local simp] ε_tensorHom_comp_μ_assoc tensorμ_comp_μ_tensorHom_μ_comp_μ_assoc
  MonObj.tensorObj.one_def MonObj.tensorObj.mul_def in
instance [F.Braided] : F.mapMon.Monoidal :=
  CoreMonoidal.toMonoidal {
    εIso := Mon_.mkIso (Monoidal.εIso F)
    μIso M N := Mon_.mkIso (Monoidal.μIso F M.X N.X) <| by simp [← Functor.map_comp]
  }

end BraidedCategory

variable [SymmetricCategory C] [SymmetricCategory D]

instance [F.LaxBraided] : F.mapMon.LaxBraided where
  braided M N := by ext; exact Functor.LaxBraided.braided ..

instance [F.Braided] : F.mapMon.Braided where

end CategoryTheory.Functor
