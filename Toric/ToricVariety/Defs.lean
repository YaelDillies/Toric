/-
Copyright (c) 2025 Yaël Dillies, Paul Lezeau, Patrick Luo, Michał Mrugała, Andrew Yang.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Paul Lezeau, Patrick Luo, Michał Mrugała, Andrew Yang
-/
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Mathlib.CategoryTheory.Monoidal.Grp_
import Mathlib.CategoryTheory.Monoidal.Mod_
import Toric.GroupScheme.Torus

/-!
# Toric varieties

This file defines a toric variety with torus `T` over a scheme `S` as a scheme `X` with an
dominant open embedding `T → X` over `S` and an action `T × X → X` extending the multiplication on
`T`.
-/

attribute [instance] Mod_Class.regular

open CategoryTheory Mon_Class MonoidalCategory CartesianMonoidalCategory Limits
  AlgebraicGeometry.Scheme

namespace AlgebraicGeometry
universe u
variable {𝕜 : Type u} [Field 𝕜] {T X : Scheme.{u}}

/-- A toric variety over a scheme `S` is a scheme `X` equipped with a torus `T`, a dense embedding
`T → X` and an action `T × X → X` extending the standard action `T × T → T`. -/
class ToricVariety (𝕜 : Type u) [Field 𝕜] (X : Scheme.{u}) extends X.Over Spec(𝕜) where
  /-- The torus. -/
  torus : Scheme.{u}
  [torusIsOver : torus.Over Spec(𝕜)]
  [grp_ClassTorus : Grp_Class (torus.asOver Spec(𝕜))]
  [mod_ClassTorus : Mod_Class (torus.asOver Spec(𝕜)) (X.asOver Spec(𝕜))]
  [torusIsTorusOver : torus.IsTorusOver 𝕜]
  /-- The torus embedding. -/
  torusEmb (𝕜 X) : torus ⟶ X
  [isOver_torusEmb : torusEmb.IsOver Spec(𝕜)]
  /-- The torus embedding is an open immersion. -/
  [isOpenImmersion_torusEmb : IsOpenImmersion torusEmb]
  /-- The torus embedding is dominant. -/
  [isDominant_torusEmb : IsDominant torusEmb]
  /-- The torus action extends the torus multiplication. -/
  torusMul_comp_torusEmb :
    (𝟙 (torus.asOver Spec(𝕜)) ⊗ₘ torusEmb.asOver Spec(𝕜)) ≫
      γ[torus.asOver Spec(𝕜), X.asOver Spec(𝕜)] = μ ≫ torusEmb.asOver Spec(𝕜) := by aesop_cat

namespace ToricVariety
variable [T.Over Spec(𝕜)] [Grp_Class (T.asOver Spec(𝕜))] [T.IsTorusOver 𝕜]

/-- A torus `T` is a toric variety over itself. -/
noncomputable instance : ToricVariety 𝕜 T where
  torus := T
  torusEmb := 𝟙 _

variable (k T) in
@[simp] lemma torusEmb_self : torusEmb 𝕜 T = 𝟙 T := rfl

end ToricVariety
end AlgebraicGeometry
