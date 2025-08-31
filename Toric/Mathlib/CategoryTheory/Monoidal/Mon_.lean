import Mathlib.CategoryTheory.Monoidal.Mon_

open CategoryTheory MonoidalCategory

assert_not_exists CartesianMonoidalCategory

namespace CategoryTheory.Functor

variable {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D] {M X : C}
  [Mon_Class M] {F : C ⥤ D}

open LaxMonoidal OplaxMonoidal

/-! ### Essential image computation -/

open Monoidal in
/-- The essential image of a fully faithful functor between cartesian-monoidal categories is the
same on monoid objects as on objects. -/
@[simp] lemma essImage_mapMon [F.Monoidal] [F.Full] [F.Faithful] {M : Mon_ D} :
    F.mapMon.essImage M ↔ F.essImage M.X where
  mp := by rintro ⟨N, ⟨e⟩⟩; exact ⟨N.X, ⟨(Mon_.forget _).mapIso e⟩⟩
  mpr := by
    rintro ⟨N, ⟨e⟩⟩
    letI h₁ := Mon_Class.ofIso e.symm
    letI h₂ := FullyFaithful.mon_Class (.ofFullyFaithful F) (X := N)
    refine ⟨.mk N, ⟨Mon_.mkIso e ?_ ?_⟩⟩ <;> simp [Mon_Class.ofIso, FullyFaithful.mon_Class, h₁, h₂]

/-! ### `mapMon` is braided -/

open scoped Obj

attribute [local simp] ε_tensorHom_comp_μ_assoc in
instance [F.LaxMonoidal] : IsMon_Hom (ε F) where

section BraidedCategory
variable [BraidedCategory C] [BraidedCategory D] (F)

attribute [-simp] IsMon_Hom.one_hom_assoc in
attribute [local simp] tensorμ_comp_μ_tensorHom_μ_comp_μ_assoc Mon_Class.tensorObj.one_def
  Mon_Class.tensorObj.mul_def in
instance [F.LaxBraided] (M N : C) [Mon_Class M] [Mon_Class N] : IsMon_Hom («μ» F M N) where
  one_hom := by simp [← Functor.map_comp, leftUnitor_inv_comp_tensorHom_assoc]

attribute [-simp] IsMon_Hom.one_hom IsMon_Hom.one_hom_assoc IsMon_Hom.mul_hom in
attribute [local simp] ε_tensorHom_comp_μ_assoc tensorμ_comp_μ_tensorHom_μ_comp_μ_assoc
  Mon_Class.tensorObj.one_def Mon_Class.tensorObj.mul_def in
instance [F.LaxBraided] : F.mapMon.LaxMonoidal where
  ε := .mk (ε F)
  μ M N := .mk («μ» F M.X N.X)

attribute [-simp] IsMon_Hom.one_hom IsMon_Hom.one_hom_assoc IsMon_Hom.mul_hom in
attribute [local simp] ε_tensorHom_comp_μ_assoc tensorμ_comp_μ_tensorHom_μ_comp_μ_assoc
  Mon_Class.tensorObj.one_def Mon_Class.tensorObj.mul_def in
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
