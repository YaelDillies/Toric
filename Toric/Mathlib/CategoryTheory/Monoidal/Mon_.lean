/-
Copyright (c) 2025 Yaël Dillies, Michał Mrugała, Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Michał Mrugała, Andrew Yang
-/
import Mathlib.CategoryTheory.Monoidal.Mon_
import Toric.Mathlib.CategoryTheory.Monoidal.Category
import Toric.Mathlib.CategoryTheory.Monoidal.Functor

open CategoryTheory MonoidalCategory Monoidal

assert_not_exists CartesianMonoidalCategory

namespace Mon_Class
variable {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]
  {M N X Y Z : C} [Mon_Class M] [Mon_Class N] (F : C ⥤ D)

def ofIso (e : M ≅ X) : Mon_Class X where
  one := η[M] ≫ e.hom
  mul := (e.inv ⊗ e.inv) ≫ μ[M] ≫ e.hom
  one_mul' := by
    rw [← cancel_epi (λ_ X).inv]
    simp only [comp_whiskerRight, tensorHom_def, Category.assoc,
      hom_inv_whiskerRight_assoc]
    simp [← tensorHom_def_assoc]
  mul_one' := by
    rw [← cancel_epi (ρ_ X).inv]
    simp only [MonoidalCategory.whiskerLeft_comp, tensorHom_def', Category.assoc,
      whiskerLeft_hom_inv_assoc, Iso.inv_hom_id]
    simp [← tensorHom_def'_assoc]
  mul_assoc' := by simpa [← id_tensorHom, ← tensorHom_id, ← tensor_comp_assoc,
      -associator_conjugation, associator_naturality_assoc] using
      congr(((e.inv ⊗ e.inv) ⊗ e.inv) ≫ $(Mon_Class.mul_assoc M) ≫ e.hom)

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
  mul_comm' := by
    simp [← IsIso.inv_comp_eq, tensorμ, ← associator_inv_naturality_left_assoc,
      ← associator_naturality_right_assoc, SymmetricCategory.braiding_swap_eq_inv_braiding M N,
      ← tensorHom_def_assoc, -whiskerRight_tensor, -tensor_whiskerLeft, ← tensor_comp,
      Mon_Class.tensorObj.mul_def]

end Mon_Class

namespace Mon_
variable {C : Type*} [Category C] [MonoidalCategory C] [BraidedCategory C]

@[simp] lemma tensorObj_X (M N : Mon_ C) : (M ⊗ N).X = M.X ⊗ N.X := rfl

end Mon_

namespace CategoryTheory.Functor

variable {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D] {M X : C}
  [Mon_Class M] {F : C ⥤ D}

open LaxMonoidal OplaxMonoidal

open scoped Mon_Class in
def FullyFaithful.mon_Class [F.OplaxMonoidal] (hF : F.FullyFaithful) (X : C) [Mon_Class (F.obj X)] :
    Mon_Class X where
  one := hF.preimage <| OplaxMonoidal.η F ≫ η[F.obj X]
  mul := hF.preimage <| OplaxMonoidal.δ F X X ≫ μ[F.obj X]
  one_mul' := hF.map_injective <| by simp [← δ_natural_left_assoc]
  mul_one' := hF.map_injective <| by simp [← δ_natural_right_assoc]
  mul_assoc' := hF.map_injective <| by simp [← δ_natural_left_assoc, ← δ_natural_right_assoc]

open Monoidal in
/-- The essential image of a full and faithful functor between cartesian-monoidal categories is the
same on group objects as on objects. -/
@[simp] lemma essImage_mapMon [F.Monoidal] [F.Full] [F.Faithful] {M : Mon_ D} :
    F.mapMon.essImage M ↔ F.essImage M.X where
  mp := by rintro ⟨N, ⟨e⟩⟩; exact ⟨N.X, ⟨(Mon_.forget _).mapIso e⟩⟩
  mpr := by
    rintro ⟨N, ⟨e⟩⟩
    letI h₁ := Mon_Class.ofIso e.symm
    letI h₂ := FullyFaithful.mon_Class (.ofFullyFaithful F) (X := N)
    refine ⟨.mk N, ⟨Mon_.mkIso e ?_ ?_⟩⟩ <;> simp [Mon_Class.ofIso, FullyFaithful.mon_Class, h₁, h₂]

variable [BraidedCategory C] [BraidedCategory D] (F)

@[reassoc]
lemma tensorμ_tensorHom_μ_μ_μ {W X Y Z : C} [F.LaxBraided] :
    tensorμ (F.obj W) (F.obj X) (F.obj Y) (F.obj Z) ≫
    (μ F W Y ⊗ μ F X Z) ≫ μ F (W ⊗ Y) (X ⊗ Z) = (μ F W X ⊗ μ F Y Z) ≫ μ F (W ⊗ X) (Y ⊗ Z) ≫
      F.map (tensorμ W X Y Z) := by
  rw [tensorHom_def]
  simp only [tensorμ, Category.assoc]
  rw [whiskerLeft_μ_μ,
    associator_inv_naturality_left_assoc, ← pentagon_inv_assoc,
    ← comp_whiskerRight_assoc, ← comp_whiskerRight_assoc, Category.assoc, whiskerRight_μ_μ,
    whiskerLeft_hom_inv_assoc, Iso.inv_hom_id_assoc, comp_whiskerRight_assoc,
    comp_whiskerRight_assoc, μ_natural_left_assoc, associator_inv_naturality_middle_assoc,
    ← comp_whiskerRight_assoc, ← comp_whiskerRight_assoc, ← MonoidalCategory.whiskerLeft_comp,
    ← Functor.LaxBraided.braided,
    MonoidalCategory.whiskerLeft_comp_assoc, μ_natural_right, whiskerLeft_μ_μ_assoc,
    comp_whiskerRight_assoc, comp_whiskerRight_assoc, comp_whiskerRight_assoc,
    comp_whiskerRight_assoc, pentagon_inv_assoc, μ_natural_left_assoc, μ_natural_left_assoc,
    Iso.hom_inv_id_assoc, ← associator_inv_naturality_left_assoc, whiskerRight_μ_μ_assoc,
    Iso.inv_hom_id_assoc, ← tensorHom_def_assoc]
  simp only [← map_comp, whisker_assoc, Category.assoc, pentagon_inv_inv_hom_hom_inv,
    pentagon_inv_hom_hom_hom_inv_assoc]

attribute [local instance] obj.instMon_Class

open scoped Mon_Class

attribute [-simp] IsMon_Hom.one_hom IsMon_Hom.one_hom_assoc IsMon_Hom.mul_hom in
attribute [simp] tensorHom_ε_left_μ_assoc tensorμ_tensorHom_μ_μ_μ_assoc
  Mon_Class.tensorObj.one_def Mon_Class.tensorObj.mul_def in
instance [F.LaxBraided] : F.mapMon.LaxMonoidal where
  ε' := .mk (ε F)
  μ' M N := .mk («μ» F M.X N.X) <| by simp [← Functor.map_comp]

attribute [-simp] IsMon_Hom.one_hom IsMon_Hom.one_hom_assoc IsMon_Hom.mul_hom in
attribute [simp] tensorHom_ε_left_μ_assoc tensorμ_tensorHom_μ_μ_μ_assoc
  Mon_Class.tensorObj.one_def Mon_Class.tensorObj.mul_def in
instance [F.Braided] : F.mapMon.Monoidal :=
  CoreMonoidal.toMonoidal {
    εIso := Mon_.mkIso (Monoidal.εIso F)
    μIso M N := Mon_.mkIso (Monoidal.μIso F M.X N.X) <| by simp [← Functor.map_comp]
  }

end CategoryTheory.Functor

namespace Mon_
variable {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]
  [SymmetricCategory C] [SymmetricCategory D] {M N X : C} [Mon_Class M] [Mon_Class N] (F : C ⥤ D)

instance [F.LaxBraided] : F.mapMon.LaxBraided where
  braided M N := by ext; exact Functor.LaxBraided.braided ..

instance [F.Braided] : F.mapMon.Braided where

@[simp] lemma braiding_hom_hom (M N : Mon_ C) : (β_ M N).hom.hom = (β_ M.X N.X).hom := rfl
@[simp] lemma braiding_inv_hom (M N : Mon_ C) : (β_ M N).inv.hom = (β_ M.X N.X).inv := rfl

end Mon_

section
variable {C : Type*} [Category C] [MonoidalCategory C] [BraidedCategory C] {M : C}

instance Mon_.mk'.X.instIsComm_Mon [Mon_Class M] [IsCommMon M] : IsCommMon (Mon_.mk M).X := ‹_›

end
