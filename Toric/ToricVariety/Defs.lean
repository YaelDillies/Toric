/-
Copyright (c) 2025 Yaël Dillies, Patrick Luo, Michał Mrugała. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Patrick Luo, Michał Mrugała
-/
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Toric.GroupScheme.Torus

/-!
# Toric varieties

This file defines a toric variety over a ring `R` as a scheme `X` with a structure morphism to
`Spec R`.
-/

open CategoryTheory ChosenFiniteProducts Limits AlgebraicGeometry.Scheme
open scoped Mon_Class MonoidalCategory

namespace AlgebraicGeometry
universe u
variable {R : CommRingCat.{u}} {n : ℕ}

attribute [local instance] ChosenFiniteProducts.ofFiniteProducts

--TODO: add group action axioms
--TODO: make a general definition of a group object action
variable (R n)
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
  torusAct : 𝔾ₘ[R, n] ⊗ X ⟶ X
  /-- The torus action extends the torus multiplication morphism. -/
  torusMul_comp_torusEmb : μ ≫ torusEmb = lift (fst _ _) (snd _ _ ≫ torusEmb) ≫ torusAct := by
    aesop_cat

noncomputable instance : ToricVariety R n 𝔾ₘ[R, n] where
  torusEmb := 𝟙 _
  torusAct := μ

end AlgebraicGeometry
