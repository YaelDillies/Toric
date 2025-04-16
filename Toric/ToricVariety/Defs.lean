/-
Copyright (c) 2025 Yaël Dillies, Patrick Luo, Michał Mrugała. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Patrick Luo, Michał Mrugała, Paul Lezeau
-/
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Toric.GroupScheme.Torus
import Toric.Mathlib.CategoryTheory.Monoidal.Cartesian.Mod_

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
variable {R : CommRingCat.{u}} (σ : Type u)

attribute [local instance] ChosenFiniteProducts.ofFiniteProducts

open Mon_Class

/-- A toric variety of dimension `n` over a ring `R` is a scheme `X` equipped with a dense embedding
`Tⁿ → X` and an action `T × X → X` extending the standard action `T × T → T`. -/
class ToricVariety (X : Over <| Spec R) where
  /-- The torus embedding -/
  torusEmb : Over.mk (SplitTorus (Spec R) σ ↘ Spec R) ⟶ X
  /-- The torus embedding is an open immersion. -/
  [isOpenImmersion_torusEmb : IsOpenImmersion torusEmb.left]
  /-- The torus embedding is dominant. -/
  [isDominant_torusEmb : IsDominant torusEmb.left]
  /-- The torus action on a toric variety. -/
  [torusAct : Mod_Class (Over.mk (SplitTorus (Spec R) σ ↘ Spec R)) X]
  /-- The torus action extends the torus multiplication morphism. -/
  torusMul_comp_torusEmb :
      (𝟙 (Over.mk (SplitTorus (Spec R) σ ↘ Spec R)) ⊗ torusEmb) ≫ γ
      =  μ[Over.mk (SplitTorus (Spec R) σ ↘ Spec R)] ≫ torusEmb :=
    by aesop_cat


noncomputable instance : ToricVariety σ (Over.mk (SplitTorus (Spec R) σ ↘ Spec R)) where
  torusEmb := 𝟙 (Over.mk (SplitTorus (Spec R) σ ↘ Spec R))
  torusAct := .regular _

end AlgebraicGeometry
