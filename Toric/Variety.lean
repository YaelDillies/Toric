/-
Copyright (c) 2025 Yaël Dillies, Patrick Luo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Patrick Luo
-/
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.CategoryTheory.Monoidal.Subcategory
import Toric.SchemeOver

/-!
# Varieties

This file defines algebraic geometric varieties over a ring `R` as separated, integral, finite type
morphisms from a scheme to `Spec R`.
-/

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry
variable {R : CommRingCat} {k : Type} [Field k] {S X Y Z : Scheme}

class IsVariety (X : Over S) : Prop where
  [isSeparated : IsSeparated X.hom]
  [isIntegral : IsIntegral X.left]
  [locallyOfFiniteType : LocallyOfFiniteType X.hom]
  [quasiCompact : QuasiCompact X.hom]

namespace IsVariety

attribute [instance] isSeparated isIntegral locallyOfFiniteType quasiCompact

end IsVariety

namespace IsVariety

instance : MonoidalPredicate (IsVariety (S := Spec R)) where
  prop_id.isSeparated := isSeparated_of_injective (𝟙_ (Over _)).hom fun ⦃a₁ a₂⦄ a ↦ a
  prop_id.isIntegral := by simp [instIsIntegralSpecOfIsDomainCarrier]; sorry
  prop_id.locallyOfFiniteType := sorry
  prop_id.quasiCompact := (quasiCompact_iff (𝟙_ (Over _)).hom).mpr (by simp)
  prop_tensor hX hY := {
    isSeparated := sorry
    isIntegral := sorry
    locallyOfFiniteType := sorry
    quasiCompact := sorry
  }

end IsVariety

variable (R) in
/-- A variety over a ring `R` is a scheme `X` along with a separated, integral, finite type morphism `f : X ⟶ Spec R`. -/
abbrev Variety := FullSubcategory fun X : Over (Spec R) ↦ IsVariety X

noncomputable instance : MonoidalCategory (Variety R) := inferInstance

end AlgebraicGeometry
