/-
Copyright (c) 2025 Yaël Dillies, Michał Mrugała, Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Michał Mrugała, Andrew Yang
-/
import Mathlib.CategoryTheory.Monoidal.Mon_

open CategoryTheory Mon_Class MonoidalCategory

assert_not_exists ChosenFiniteProducts

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

open Limits

namespace CategoryTheory.Functor
universe v₁ v₂ v₃ u₁ u₂ u₃
variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
variable {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]
variable {E : Type u₃} [Category.{v₃} E] [MonoidalCategory E]
variable (F F' : C ⥤ D) (G : D ⥤ E)

open LaxMonoidal

@[simps!]
noncomputable def mapMonIdIso : mapMon (𝟭 C) ≅ 𝟭 (Mon_ C) :=
  NatIso.ofComponents fun X ↦ Mon_.mkIso (.refl _)

@[simps!]
noncomputable def mapMonCompIso [F.LaxMonoidal] [G.LaxMonoidal] :
    (F ⋙ G).mapMon ≅ F.mapMon ⋙ G.mapMon :=
  NatIso.ofComponents fun X ↦ Mon_.mkIso (.refl _)

end CategoryTheory.Functor
