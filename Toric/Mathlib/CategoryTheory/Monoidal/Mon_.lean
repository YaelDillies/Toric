/-
Copyright (c) 2025 Yaël Dillies, Michał Mrugała, Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Michał Mrugała, Andrew Yang
-/
import Mathlib.CategoryTheory.Monoidal.Mon_
import Toric.Mathlib.CategoryTheory.Monoidal.Functor

open CategoryTheory Mon_Class MonoidalCategory

assert_not_exists CartesianMonoidalCategory

namespace CategoryTheory.Functor
variable {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D] {M X : C}
  [Mon_Class M] (F : C ⥤ D)

variable [BraidedCategory C] [BraidedCategory D]

open LaxMonoidal

instance [F.LaxBraided] : F.mapMon.LaxMonoidal where
  ε' := .mk (ε F) (by aesop_cat) <| by simp [← wiskerLeft_left_unitality]
  μ' M N := .mk («μ» F M.X N.X) sorry <| by simp; sorry
  μ'_natural_left := sorry
  μ'_natural_right := sorry
  associativity' := sorry
  left_unitality' := sorry
  right_unitality' := sorry

end CategoryTheory.Functor

namespace Mon_
variable {C : Type*} [Category C] [MonoidalCategory C] [SymmetricCategory C]

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
