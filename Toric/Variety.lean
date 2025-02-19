/-
Copyright (c) 2025 Yaël Dillies, Patrick Luo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Patrick Luo
-/
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.CategoryTheory.Monoidal.Category

/-!
# Varieties

This files defines algebraic geometric varieties over a ring `R` as separated, integral, finite type
morphisms from a scheme to `Spec R`.
-/

open CategoryTheory

namespace AlgebraicGeometry
variable {R : CommRingCat} {X Y Z : Scheme}

/-- A morphism of schemes is a variety hom if it is separated, integral and of finite type. -/
class IsVarietyHom ⦃X Y : Scheme⦄ (f : X ⟶ Y) : Prop where
  [isSeparated : IsSeparated f]
  [isIntegralHom : IsIntegralHom f]
  [locallyOfFiniteType : LocallyOfFiniteType f]
  [quasiCompact : QuasiCompact f]

namespace IsVarietyHom

attribute [instance] isSeparated isIntegralHom locallyOfFiniteType quasiCompact

@[simp] protected lemma id : IsVarietyHom (𝟙 X) where

end IsVarietyHom

variable (R) in
/-- A variety over a ring `R` is a scheme `X` along with a separated, integral, finite type morphism `f : X ⟶ Spec R`. -/
abbrev Variety := FullSubcategory fun X : Over (Spec R) ↦ IsVarietyHom X.hom

instance : MonoidalCategory (Variety R) := sorry

end AlgebraicGeometry
