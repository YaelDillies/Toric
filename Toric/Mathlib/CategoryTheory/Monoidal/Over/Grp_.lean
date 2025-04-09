/-
Copyright (c) 2025 Yaël Dillies, Michał Mrugała, Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Michał Mrugała, Andrew Yang
-/
import Mathlib.CategoryTheory.Monoidal.Yoneda
import Toric.Mathlib.CategoryTheory.ChosenFiniteProducts.Over
import Toric.Mathlib.CategoryTheory.Monoidal.Grp_

/-!
# Group objects in the over category
-/

open CategoryTheory ChosenFiniteProducts Mon_Class MonoidalCategory

variable {C : Type*} [Category C] [ChosenFiniteProducts C] {X G : C} [Grp_Class G]

-- TODO (Michał): doc string
def yonedaGrpObjRepresentableByOverMkSnd :
    ((Over.forget X).op ⋙ yonedaGrpObj G ⋙ forget Grp).RepresentableBy (.mk (snd G X)) where
  homEquiv {Y} := show (Y ⟶ Over.mk (snd G X)) ≃ (Y.left ⟶ G) from {
      toFun f := f.left ≫ fst _ _
      invFun f := Over.homMk (lift f Y.hom)
      left_inv f := by ext; simp; ext <;> simp; simpa using f.w.symm
      right_inv f := by simp
    }
  homEquiv_comp {Y Z} f g := by dsimp; erw [Equiv.coe_fn_mk, Equiv.coe_fn_mk]; simp

variable [Limits.HasPullbacks C]

attribute [local instance] Over.chosenFiniteProducts

noncomputable instance : Grp_Class <| Over.mk <| snd G X :=
  .ofRepresentableBy _ ((Over.forget _).op ⋙ yonedaGrpObj G) yonedaGrpObjRepresentableByOverMkSnd
