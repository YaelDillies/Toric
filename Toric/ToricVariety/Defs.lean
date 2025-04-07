/-
Copyright (c) 2025 Yaël Dillies, Patrick Luo, Michał Mrugała. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Patrick Luo, Michał Mrugała, Paul Lezeau
-/
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Toric.GroupScheme.Torus
import Toric.Torus
import Toric.MonoidObjectAction.Basic

/-!
# Toric varieties

This file defines a toric variety over a ring `R` as a scheme `X` with a structure morphism to
`Spec R`.
-/

open CategoryTheory Limits
open CategoryTheory Mon_Class MonoidalCategory
open CategoryTheory ChosenFiniteProducts Limits AlgebraicGeometry.Scheme
open scoped Mon_Class MonoidalCategory
namespace AlgebraicGeometry
universe u
variable {R : CommRingCat.{u}} {n : ℕ}

attribute [local instance] ChosenFiniteProducts.ofFiniteProducts

open Action_Class

/-- A toric variety of dimension `n` over a ring `R` is a scheme `X` equipped with a dense embedding
`Tⁿ → X` and an action `T × X → X` extending the standard action `T × T → T`. -/
class ToricVariety (X : Over <| Spec R) where
  /-- The torus embedding -/
  torusEmb : 𝔾ₘ[R, n] ⟶ X
  /-- The torus embedding is an open immersion. -/
  [isOpenImmersion_torusEmb : IsOpenImmersion torusEmb.left]
  /-- The torus embedding is dominant. -/
  [isDominant_torusEmb : IsDominant torusEmb.left]
  /-- The torus action on a toric variety. -/
  [torusAct : Action_Class (torusOver R n) X]
  /-- The torus action extends the torus multiplication morphism. -/
  torusMul_comp_torusEmb : (𝟙 (torusOver R n) ⊗ torusEmb) ≫ γ =  μ[torusOver R n] ≫ torusEmb :=
    by aesop_cat


noncomputable instance : ToricVariety R n (torusOver R n) where
  torusEmb := 𝟙 ((torusOver R n))
  torusAct := selfAction _

end AlgebraicGeometry
