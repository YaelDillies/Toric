import Mathlib.CategoryTheory.Monoidal.CommMon_
import Toric.Mathlib.CategoryTheory.ChosenFiniteProducts

universe v₁ v₂ u₁ u₂ u
open CategoryTheory MonoidalCategory Mon_Class

variable (C : Type u₁) [Category.{v₁} C] [MonoidalCategory.{v₁} C] [BraidedCategory.{v₁} C]

section

variable {C}

class IsCommMon (X : C) [Mon_Class X] where
  mul_comm' : (β_ X X).hom ≫ μ = μ := by aesop_cat

open scoped Mon_Class

namespace IsCommMon

@[reassoc (attr := simp)]
theorem mul_comm (X : C) [Mon_Class X] [IsCommMon X] : (β_ X X).hom ≫ μ = μ := mul_comm'

end IsCommMon

end

namespace CommMon_

variable {C}

def mk' (X : C)  [Mon_Class X] [IsCommMon X] : CommMon_ C where
  __ := Mon_.mk' X
  mul_comm := IsCommMon.mul_comm X

instance (X : CommMon_ C) : IsCommMon X.X where
  mul_comm' := X.mul_comm
