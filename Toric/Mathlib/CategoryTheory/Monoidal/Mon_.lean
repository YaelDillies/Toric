/-
Copyright (c) 2025 Yaël Dillies, Michał Mrugała, Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Michał Mrugała, Andrew Yang
-/
import Mathlib.CategoryTheory.Monoidal.Mon_
import Toric.Mathlib.CategoryTheory.Monoidal.Functor

open CategoryTheory MonoidalCategory

assert_not_exists CartesianMonoidalCategory

namespace CategoryTheory.Functor

variable {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D] {M X : C}
  [Mon_Class M] (F : C ⥤ D)

variable [BraidedCategory C] [BraidedCategory D]

open LaxMonoidal OplaxMonoidal

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

attribute [local simp] tensorHom_ε_left_μ_assoc tensorμ_tensorHom_μ_μ_μ_assoc in
instance [F.LaxBraided] : F.mapMon.LaxMonoidal where
  ε' := .mk (ε F)
  μ' M N := .mk (μ F M.X N.X)

attribute [local simp] tensorHom_ε_left_μ_assoc tensorμ_tensorHom_μ_μ_μ_assoc in
instance [F.Braided] : F.mapMon.Monoidal :=
  CoreMonoidal.toMonoidal
  { εIso := Mon_.mkIso (Monoidal.εIso F)
    μIso M N := Mon_.mkIso (Monoidal.μIso F M.X N.X) }

end CategoryTheory.Functor

namespace Mon_Class
variable {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]
  {M N X : C} [Mon_Class M] [Mon_Class N] (F : C ⥤ D)

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
      ← tensorHom_def_assoc, -whiskerRight_tensor, -tensor_whiskerLeft, ← tensor_comp]

end Mon_Class

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
variable {C : Type*} [Category C] [MonoidalCategory C]

namespace Mon_Class

theorem mul_assoc_flip (X : C) [Mon_Class X] : X ◁ μ ≫ μ = (α_ X X X).inv ≫ μ ▷ X ≫ μ := by simp

end Mon_Class

variable [BraidedCategory C] {G : C}

instance Mon_.mk'.X.instIsComm_Mon [Mon_Class G] [IsCommMon G] : IsCommMon (Mon_.mk' G).X := ‹_›

end

namespace Mon_
variable {C : Type*} [Category C] [MonoidalCategory C] {M N : Mon_ C}

-- TODO: Rewrite `Mon_.mul_assoc_flip` to this
example : (M.X ◁ M.mul) ≫ M.mul = (α_ M.X M.X M.X).inv ≫ (M.mul ▷ M.X) ≫ M.mul :=
  Mon_Class.mul_assoc_flip M.X

end Mon_
