/-
Copyright (c) 2025 Yaël Dillies, Michał Mrugała, Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Michał Mrugała, Andrew Yang
-/
import Mathlib.CategoryTheory.Monoidal.Mon_

open CategoryTheory MonoidalCategory

assert_not_exists CartesianMonoidalCategory
namespace Mon_Class
variable {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]
  {M N X Y Z : C} [Mon_Class M] [Mon_Class N] (F : C ⥤ D)

def ofIso (e : M ≅ X) : Mon_Class X where
  one := η[M] ≫ e.hom
  mul := (e.inv ⊗ₘ e.inv) ≫ μ[M] ≫ e.hom
  one_mul := by
    rw [← cancel_epi (λ_ X).inv]
    simp only [comp_whiskerRight, tensorHom_def, Category.assoc,
      hom_inv_whiskerRight_assoc]
    simp [← tensorHom_def_assoc, leftUnitor_inv_comp_tensorHom_assoc]
  mul_one := by
    rw [← cancel_epi (ρ_ X).inv]
    simp only [MonoidalCategory.whiskerLeft_comp, tensorHom_def', Category.assoc,
      whiskerLeft_hom_inv_assoc, Iso.inv_hom_id]
    simp [← tensorHom_def'_assoc, rightUnitor_inv_comp_tensorHom_assoc]
  mul_assoc := by simpa [← id_tensorHom, ← tensorHom_id, ← tensor_comp_assoc,
      -associator_conjugation, associator_naturality_assoc] using
      congr(((e.inv ⊗ₘ e.inv) ⊗ₘ e.inv) ≫ $(Mon_Class.mul_assoc M) ≫ e.hom)

variable [SymmetricCategory C] [SymmetricCategory D]

omit [SymmetricCategory C] in
@[reassoc (attr := simp)]
lemma whiskerLeft_whiskerRight_inv_hom_id {W X Y Z : C} (e : X ≅ Y) :
    W ◁ e.inv ▷ Z ≫ W ◁ e.hom ▷ Z = 𝟙 _ := by
  rw [← MonoidalCategory.whiskerLeft_comp, ← comp_whiskerRight, e.inv_hom_id]; simp

omit [SymmetricCategory C] in
@[reassoc (attr := simp)]
lemma whiskerLeft_whiskerRight_hom_inv_id {W X Y Z : C} (e : X ≅ Y) :
    W ◁ e.hom ▷ Z ≫ W ◁ e.inv ▷ Z = 𝟙 _ := by
  rw [← MonoidalCategory.whiskerLeft_comp, ← comp_whiskerRight, e.hom_inv_id]; simp

instance [IsCommMon M] [IsCommMon N] : IsCommMon (M ⊗ N) where
  mul_comm := by
    simp [← IsIso.inv_comp_eq, tensorμ, ← associator_inv_naturality_left_assoc,
      ← associator_naturality_right_assoc, SymmetricCategory.braiding_swap_eq_inv_braiding M N,
      ← tensorHom_def_assoc, -whiskerRight_tensor, -tensor_whiskerLeft, ← tensor_comp,
      Mon_Class.tensorObj.mul_def]

end Mon_Class

section
variable {C : Type*} [Category C] [MonoidalCategory C] [BraidedCategory C] {M N : C} [Mon_Class M]
  [Mon_Class N]

instance {f : M ⟶ N} [IsIso f] [IsMon_Hom f] : IsMon_Hom (asIso f).hom := ‹_›

end

namespace CategoryTheory.Functor

variable {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D] {M X : C}
  [Mon_Class M] {F : C ⥤ D}

open LaxMonoidal OplaxMonoidal

open scoped Mon_Class in
def FullyFaithful.mon_Class [F.OplaxMonoidal] (hF : F.FullyFaithful) (X : C) [Mon_Class (F.obj X)] :
    Mon_Class X where
  one := hF.preimage <| OplaxMonoidal.η F ≫ η[F.obj X]
  mul := hF.preimage <| OplaxMonoidal.δ F X X ≫ μ[F.obj X]
  one_mul := hF.map_injective <| by simp [← δ_natural_left_assoc]
  mul_one := hF.map_injective <| by simp [← δ_natural_right_assoc]
  mul_assoc := hF.map_injective <| by simp [← δ_natural_left_assoc, ← δ_natural_right_assoc]

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

open scoped Obj

attribute [local simp] ε_tensorHom_comp_μ_assoc in
instance [F.LaxMonoidal] : IsMon_Hom (ε F) where

section BraidedCategory
variable [BraidedCategory C] [BraidedCategory D] (F)

attribute [-simp] IsMon_Hom.one_hom_assoc in
attribute [simp] tensorμ_comp_μ_tensorHom_μ_comp_μ_assoc Mon_Class.tensorObj.one_def
  Mon_Class.tensorObj.mul_def in
instance [F.LaxBraided] (M N : C) [Mon_Class M] [Mon_Class N] : IsMon_Hom («μ» F M N) where
  one_hom := by simp [← Functor.map_comp, leftUnitor_inv_comp_tensorHom_assoc]

attribute [-simp] IsMon_Hom.one_hom IsMon_Hom.one_hom_assoc IsMon_Hom.mul_hom in
attribute [simp] ε_tensorHom_comp_μ_assoc tensorμ_comp_μ_tensorHom_μ_comp_μ_assoc
  Mon_Class.tensorObj.one_def Mon_Class.tensorObj.mul_def in
instance [F.LaxBraided] : F.mapMon.LaxMonoidal where
  ε := .mk (ε F)
  μ M N := .mk («μ» F M.X N.X)

attribute [-simp] IsMon_Hom.one_hom IsMon_Hom.one_hom_assoc IsMon_Hom.mul_hom in
attribute [simp] ε_tensorHom_comp_μ_assoc tensorμ_comp_μ_tensorHom_μ_comp_μ_assoc
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
