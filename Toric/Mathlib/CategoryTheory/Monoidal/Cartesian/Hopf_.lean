/-
Copyright (c) 2025 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.CategoryTheory.Monoidal.Grp_
import Mathlib.CategoryTheory.Monoidal.Cartesian.Comon_
import Mathlib.CategoryTheory.Monoidal.Hopf_

/-!
# TODO

Make `antipode_left`/`antipode_right` auto-param to `aesop_cat`?
-/

noncomputable section

universe v₁ v₂ u₁ u₂ u

open CategoryTheory MonoidalCategory ChosenFiniteProducts Limits

variable (C : Type u₁) [Category.{v₁} C] [ChosenFiniteProducts C] [BraidedCategory C]

def hopfEquivGrp : Hopf_ C ≌ Grp_ C where
  functor.obj H := {
      toMon_ := H.X.X
      inv := H.antipode
      left_inv := by
        stop
        have := H.antipode_left
        erw [comul_eq_diag (C := Mon_ C) ] at this
        simpa [-Hopf_.antipode_left] using H.antipode_left
      right_inv := sorry
    }
  functor.map := sorry
  functor.map_id := sorry
  functor.map_comp := sorry
  inverse := sorry
  unitIso := sorry
  counitIso := sorry
  functor_unitIso_comp := sorry
