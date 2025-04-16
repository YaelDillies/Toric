/-
Copyright (c) 2025 Yaël Dillies, Michał Mrugała, Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Michał Mrugała, Andrew Yang
-/
import Mathlib.CategoryTheory.Monoidal.Yoneda
import Mathlib.CategoryTheory.ChosenFiniteProducts.Over

/-!
# Monoid objects in the over category
-/

open CategoryTheory ChosenFiniteProducts Mon_Class MonoidalCategory

variable {C : Type*} [Category C] [ChosenFiniteProducts C] {X G : C} [Mon_Class G]

-- TODO (Michał): doc string
def yonedaMonObjMon_ClassOfRepresentableBy :
    ((Over.forget X).op ⋙ yonedaMonObj G ⋙ forget MonCat).RepresentableBy (.mk (snd G X)) where
  homEquiv {Y} := show (Y ⟶ Over.mk (snd G X)) ≃ (Y.left ⟶ G) from {
      toFun f := f.left ≫ fst _ _
      invFun f := Over.homMk (lift f Y.hom)
      left_inv f := by ext; simp; ext <;> simp; simpa using f.w.symm
      right_inv f := by simp
    }
  homEquiv_comp {Y Z} f g := by dsimp; erw [Equiv.coe_fn_mk, Equiv.coe_fn_mk]; simp

variable [Limits.HasPullbacks C]

attribute [local instance] Over.chosenFiniteProducts

noncomputable instance : Mon_Class <| Over.mk <| snd G X :=
  Mon_Class.ofRepresentableBy _ ((Over.forget _).op ⋙ yonedaMonObj G)
      yonedaMonObjMon_ClassOfRepresentableBy
