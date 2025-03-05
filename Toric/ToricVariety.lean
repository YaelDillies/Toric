/-
Copyright (c) 2025 Yaël Dillies, Patrick Luo, Michał Mrugała. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Patrick Luo, Michał Mrugała
-/
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Toric.Torus

/-!
# Toric varieties

This file defines a toric variety over a ring `R` as a scheme `X` with a structure morphism to
`Spec R`.
-/

open CategoryTheory Limits

namespace AlgebraicGeometry
variable {R : CommRingCat} {n : ℕ}

variable (R n)
/-- A toric variety of dimension `n` over a ring `R` is a scheme `X` equipped with a dense embedding
`Tⁿ → X` and an action `T × X → X` extending the standard action `T × T → T`. -/
class ToricVariety (X : Scheme) extends X.Over (Spec R) where
  /-- The torus embedding -/
  torusEmb : Torus R n ⟶ X
  /-- The torus embedding is a morphism over `Spec R`. -/
  torusEmb_comp_overHom : torusEmb ≫ X ↘ Spec R = Torus R n ↘ Spec R := by aesop_cat
  /-- The torus embedding is an open immersion. -/
  [isOpenImmersion_torusEmb : IsOpenImmersion torusEmb]
  /-- The torus embedding is dominant. -/
  [isDominant_torusEmb : IsDominant torusEmb]
  /-- The torus action on a toric variety. -/
  torusAct : pullback (Torus R n ↘ Spec R) (X ↘ Spec R) ⟶ X
  /-- The torus action extends the torus multiplication morphism. -/
  torusMul_comp_torusEmb :
    torusMul ≫
    torusEmb = pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ torusEmb)
                (by simp [pullback.condition, torusEmb_comp_overHom]) ≫
    torusAct := by aesop_cat

noncomputable instance : ToricVariety R n (Torus R n) where
  torusEmb := 𝟙 (Torus R n)
  torusAct := torusMul

end AlgebraicGeometry
