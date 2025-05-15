/-
Copyright (c) 2025 Yaël Dillies, Michał Mrugała, Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Michał Mrugała, Andrew Yang
-/
import Mathlib.CategoryTheory.Monoidal.Mon_

open CategoryTheory Mon_Class MonoidalCategory

assert_not_exists CartesianMonoidalCategory

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
