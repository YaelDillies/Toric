/-
Copyright (c) 2025 Yaël Dillies, Michał Mrugała, Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Michał Mrugała, Andrew Yang
-/
import Mathlib.CategoryTheory.Monoidal.Cartesian.Mon_

open CategoryTheory MonObj

/-! ### Comm monoid objects are internal monoid objects -/

namespace Mon
variable {C : Type*} [Category C] [CartesianMonoidalCategory C] [BraidedCategory C]
  {M N N₁ N₂ : Mon C}

/-- A commutative monoid object is a monoid object in the category of monoid objects. -/
instance [IsCommMonObj M.X] : MonObj M where
  one := .mk η[M.X]
  mul := .mk μ[M.X]

@[simp] lemma hom_one (M : Mon C) [IsCommMonObj M.X] : η[M].hom = η[M.X] := rfl
@[simp] lemma hom_mul (M : Mon C) [IsCommMonObj M.X] : μ[M].hom = μ[M.X] := rfl

namespace Hom
variable [IsCommMonObj N.X]

@[simp] lemma hom_one : (1 : M ⟶ N).hom = 1 := rfl

@[simp] lemma hom_mul (f g : M ⟶ N) : (f * g).hom = f.hom * g.hom := rfl

@[simp] lemma hom_pow (f : M ⟶ N) (n : ℕ) : (f ^ n).hom = f.hom ^ n := by
  induction n <;> simp [pow_succ, *]

end Hom

/-- A commutative monoid object is a commutative monoid object in the category of monoid objects. -/
instance [IsCommMonObj M.X] : IsCommMonObj M where

end Mon
