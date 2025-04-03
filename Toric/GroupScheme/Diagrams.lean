/-
Copyright (c) 2025 Yaël Dillies, Michał Mrugała. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Michał Mrugała
-/
import Toric.Mathlib.CategoryTheory.Monoidal.Mon_

open CategoryTheory Mon_Class MonoidalCategory

namespace Mon_

variable {C : Type*} [Category C] [ChosenFiniteProducts C] {M N : Mon_ C}

variable [IsCommMon N.X]

lemma gigaDiagram :
    (α_ _ _ _).hom
    ≫ M.X ◁ (α_ _ _ _).inv
    ≫ M.X ◁ (M.mul ▷ M.X)
    ≫ M.X ◁ M.mul
    ≫ M.mul
      = (M.mul ⊗ M.mul)
        ≫ M.mul := calc
  _ = (α_ _ _ _).hom
        ≫ M.X ◁ ((α_ _ _ _).inv ≫ M.mul ▷ M.X ≫ M.mul)
        ≫ M.mul := by simp [-Mon_.mul_assoc]
  _ = (α_ _ _ _).hom
        ≫ M.X ◁ M.X ◁ M.mul
        ≫ M.X ◁ M.mul
        ≫ M.mul := by
    simp [M.mul_assoc]
  _ = (M.X ⊗ M.X) ◁ M.mul
        ≫ (α_ _ _ _).hom
        ≫ M.X ◁ M.mul
        ≫ M.mul := by simp
  _ = (M.X ⊗ M.X) ◁ M.mul
        ≫ M.mul ▷ M.X
        ≫ M.mul := by simp
  _ = (M.mul ⊗ M.mul) ≫ M.mul := by
    rw [tensorHom_def']
    simp

lemma gigaDiagram2 :
    (α_ _ _ _).hom
    ≫ N.X ◁ (α_ _ _ _).inv
    ≫ N.X ◁ ((β_ _ _).hom ▷ N.X)
    ≫ N.X ◁ (N.mul ▷ N.X)
    ≫ N.X ◁ N.mul
    ≫ N.mul
      = (α_ _ _ _).hom
        ≫ N.X ◁ (α_ _ _ _).inv
        ≫ N.X ◁ (N.mul ▷ N.X)
        ≫ N.X ◁ N.mul
        ≫ N.mul := calc
  _ = (α_ _ _ _).hom
    ≫ N.X ◁ (α_ _ _ _).inv
    ≫ N.X ◁ (((β_ _ _).hom ≫ N.mul) ▷ N.X)
    ≫ N.X ◁ N.mul
    ≫ N.mul := by simp
  _ = (α_ _ _ _).hom
        ≫ N.X ◁ (α_ _ _ _).inv
        ≫ N.X ◁ (N.mul ▷ N.X)
        ≫ N.X ◁ N.mul
        ≫ N.mul := by
    have : N.mul = μ := rfl
    rw [this]
    rw [IsCommMon.mul_comm N.X]

lemma gigaDiagram3 :
    (α_ _ _ _).hom
    ≫ M.X ◁ (α_ _ _ _).inv
    ≫ M.X ◁ ((β_ _ _).hom ▷ M.X)
    ≫ M.X ◁ (α_ _ _ _).hom
    ≫ (α_ _ _ _).inv
    ≫ (α_ _ _ _).hom
    ≫ M.X ◁ (α_ _ _ _).inv
    ≫ M.X ◁ (M.mul ▷ M.X)
    ≫ M.X ◁ M.mul
    ≫ M.mul
      = (α_ _ _ _).hom
        ≫ M.X ◁ (α_ _ _ _).inv
        ≫ M.X ◁ ((β_ _ _).hom ▷ M.X)
        ≫ M.X ◁ (M.mul ▷ M.X)
        ≫ M.X ◁ M.mul
        ≫ M.mul := by simp

lemma gigaDiagram4 :
    (α_ _ _ _).hom
    ≫ M.X ◁ (α_ _ _ _).inv
    ≫ M.X ◁ ((β_ _ _).hom ▷ M.X)
    ≫ M.X ◁ (α_ _ _ _).hom
    ≫ (α_ _ _ _).inv
    ≫ (α_ _ _ _).hom
    ≫ M.X ◁ (α_ _ _ _).inv
    ≫ M.X ◁ (M.mul ▷ M.X)
    ≫ M.X ◁ M.mul
    ≫ M.mul
      = (α_ _ _ _).hom
        ≫ M.X ◁ (α_ _ _ _).inv
        ≫ M.X ◁ ((β_ _ _).hom ▷ M.X)
        ≫ M.X ◁ (α_ _ _ _).hom
        ≫ (α_ _ _ _).inv
        ≫ (M.mul ⊗ M.mul)
        ≫ M.mul := by
  rw [gigaDiagram]

lemma gigaOmegaDiagram :
    (N.mul ⊗ N.mul)
    ≫ N.mul
      = (α_ _ _ _).hom
        ≫ N.X ◁ (α_ _ _ _).inv
        ≫ N.X ◁ ((β_ _ _).hom ▷ N.X)
        ≫ N.X ◁ (α_ _ _ _).hom
        ≫ (α_ _ _ _).inv
        ≫ (N.mul ⊗ N.mul)
        ≫ N.mul := by
  nth_rewrite 1 [← gigaDiagram, ← gigaDiagram2, ← gigaDiagram3, gigaDiagram4]
  simp

end Mon_
