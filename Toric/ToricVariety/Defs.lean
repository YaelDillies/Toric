/-
Copyright (c) 2025 Yaël Dillies, Paul Lezeau, Patrick Luo, Michał Mrugała. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Paul Lezeau, Patrick Luo, Michał Mrugała
-/
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Mathlib.CategoryTheory.Monoidal.Mod_
import Toric.GroupScheme.Torus

/-!
# Toric varieties

This file defines a toric variety over a ring `R` as a scheme `X` with a structure morphism to
`Spec R`.
-/

open CategoryTheory Mon_Class MonoidalCategory CartesianMonoidalCategory Limits
  AlgebraicGeometry.Scheme

namespace AlgebraicGeometry
universe u
variable {R : CommRingCat.{u}} (σ : Type u)

open Mon_Class

variable (R) in
/-- A toric variety of dimension `n` over a ring `R` is a scheme `X` equipped with a dense embedding
`Tⁿ → X` and an action `T × X → X` extending the standard action `T × T → T`. -/
class ToricVariety (X : Scheme)
    extends X.Over (Spec R), Mod_Class 𝔾ₘ[R, σ] (asOver X (Spec R)) where
  /-- The torus embedding. -/
  torusEmb : 𝔾ₘ[R, σ] ⟶ asOver X (Spec R)
  /-- The torus embedding is an open immersion. -/
  [isOpenImmersion_torusEmb : IsOpenImmersion torusEmb.left]
  /-- The torus embedding is dominant. -/
  [isDominant_torusEmb : IsDominant torusEmb.left]
  /-- The torus action extends the torus multiplication morphism. -/
  torusMul_comp_torusEmb : (𝟙 𝔾ₘ[R, σ] ⊗ torusEmb) ≫ γ =  μ[𝔾ₘ[R, σ]] ≫ torusEmb := by aesop_cat

noncomputable instance : ToricVariety R σ 𝔾ₘ[R, σ].left where
  toMod_Class := .regular _
  torusEmb := 𝟙 _

end AlgebraicGeometry
