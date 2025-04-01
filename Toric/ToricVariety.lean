/-
Copyright (c) 2025 Yaël Dillies, Patrick Luo, Michał Mrugała. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Patrick Luo, Michał Mrugała
-/
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Toric.Torus
import Toric.MonoidObjectAction.Basic

/-!
# Toric varieties

This file defines a toric variety over a ring `R` as a scheme `X` with a structure morphism to
`Spec R`.
-/

open CategoryTheory Limits
open CategoryTheory Mon_Class MonoidalCategory

namespace AlgebraicGeometry
variable {R : CommRingCat} {n : ℕ}

open Action_Class

--TODO: add group action axioms
--TODO: make a general definition of a group object action
variable (R n)
-- /-- A toric variety of dimension `n` over a ring `R` is a scheme `X` equipped with a dense
--embedding
-- `Tⁿ → X` and an action `T × X → X` extending the standard action `T × T → T`. -/
-- class ToricVariety (X : Scheme) extends X.Over (Spec R) where
--   /-- The torus embedding -/
--   torusEmb : Torus R n ⟶ X
--   /-- The torus embedding is a morphism over `Spec R`. -/
--   torusEmb_comp_overHom : HomIsOver torusEmb (Spec R) := by aesop_cat
--   /-- The torus embedding is an open immersion. -/
--   [isOpenImmersion_torusEmb : IsOpenImmersion torusEmb]
--   /-- The torus embedding is dominant. -/
--   [isDominant_torusEmb : IsDominant torusEmb]
--   [torusAct : Action_Class (torusOver R n) (X.asOver <| Spec R)]
--   /- The torus action on a toric variety. -/
--   --torusAct : pullback (Torus R n ↘ Spec R) (X ↘ Spec R) ⟶ X
--   /-- The torus action extends the torus multiplication morphism. -/
--   torusMul_comp_torusEmb : (𝟙 (torusOver R n)) ⊗ (Scheme.Hom.asOver torusEmb (Spec R)) ≫
--       (γ : (torusOver R n) ⊗ (X.asOver <| Spec R) ⟶ (X.asOver <| Spec R)) =
--         μ[(torusOver R n)] ≫ (Scheme.Hom.asOver torusEmb (Spec R))
--     -- torusMul ≫
--     -- torusEmb = pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ torusEmb)
--     --             (by simp [pullback.condition, torusEmb_comp_overHom]) ≫
--     -- torusAct := by aesop_cat
--   /-There is a monoid action of the torus on `X` -/
--  --torusAction : Action_Class (torusOver R n) (X.asOver <| Spec R)
--   /-- The torus action is compatible with the torus embedding -/
--   t : Bool

/-- A toric variety of dimension `n` over a ring `R` is a scheme `X` equipped with a dense embedding
`Tⁿ → X` and an action `T × X → X` extending the standard action `T × T → T`. -/
class ToricVariety (X : Over <| Spec R) where
  /-- The torus embedding -/
  torusEmb : torusOver R n ⟶ X
  /-- The torus embedding is an open immersion. -/
  [isOpenImmersion_torusEmb : IsOpenImmersion torusEmb.left]
  /-- The torus embedding is dominant. -/
  [isDominant_torusEmb : IsDominant torusEmb.left]
  /-- The torus action on a toric variety. -/
  [torusAct : Action_Class (torusOver R n) X]
  /-- The torus action extends the torus multiplication morphism. -/
  torusMul_comp_torusEmb : (𝟙 (torusOver R n) ⊗ torusEmb) ≫ γ =  μ[(torusOver R n)] ≫ torusEmb :=
    by aesop_cat


noncomputable instance : ToricVariety R n (torusOver R n) where
  torusEmb := 𝟙 ((torusOver R n))
  torusAct := selfAction _

end AlgebraicGeometry
