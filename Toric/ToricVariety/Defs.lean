/-
Copyright (c) 2025 Yaël Dillies, Paul Lezeau, Patrick Luo, Michał Mrugała, Andrew Yang.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Paul Lezeau, Patrick Luo, Michał Mrugała, Andrew Yang
-/
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Mathlib.CategoryTheory.Monoidal.Grp_
import Mathlib.CategoryTheory.Monoidal.Mod_
import Toric.Mathlib.CategoryTheory.Comma.Over.OverClass

/-!
# Toric varieties

This file defines a toric variety with torus `T` over a scheme `S` as a scheme `X` with an
dominant open embedding `T → X` over `S` and an action `T × X → X` extending the multiplication on
`T`.
-/

open CategoryTheory Mon_Class MonoidalCategory CartesianMonoidalCategory Limits
  AlgebraicGeometry.Scheme

namespace AlgebraicGeometry
universe u
variable {S T X : Scheme.{u}} [T.Over S] [Grp_Class (T.asOver S)]

/-- A toric variety with torus `T` over a scheme `S` is a scheme `X` equipped with a dense embedding
`T → X` and an action `T × X → X` extending the standard action `T × T → T`

Note that we do not assume `T` to be a torus within the definition. -/
class ToricVariety (S T X : Scheme.{u}) [tOverS : T.Over S] [grpT : Grp_Class (T.asOver S)]
    extends X.Over S, Mod_Class (T.asOver S) (X.asOver S) where
  /-- The torus embedding. -/
  torusEmb [tOverS] [grpT] : T ⟶ X
  [isOver_torusEmb : torusEmb.IsOver S]
  /-- The torus embedding is an open immersion. -/
  [isOpenImmersion_torusEmb : IsOpenImmersion torusEmb]
  /-- The torus embedding is dominant. -/
  [isDominant_torusEmb : IsDominant torusEmb]
  /-- The torus action extends the torus multiplication. -/
  torusMul_comp_torusEmb : (𝟙 (T.asOver S) ⊗ torusEmb.asOver S) ≫ γ = μ ≫ torusEmb.asOver S := by
   aesop_cat

namespace ToricVariety

/-- A torus `T` is a toric variety over itself. -/
noncomputable instance : ToricVariety S T T where
  toMod_Class := .regular _
  torusEmb := 𝟙 _

variable (k T) in
@[simp] lemma torusEmb_self : torusEmb S = 𝟙 T := rfl

end ToricVariety
end AlgebraicGeometry
