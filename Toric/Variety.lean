/-
Copyright (c) 2025 Yaël Dillies, Patrick Luo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Patrick Luo
-/
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib

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

noncomputable instance : MonoidalCategory (Variety R) where
  tensorObj := fun X Y ↦ ⟨.mk (Limits.pullback.fst X.obj.hom Y.obj.hom ≫ X.obj.hom), sorry⟩
  whiskerLeft := by
    rintro X Y₁ Y₂ f
    refine Over.homMk (CategoryTheory.Limits.pullback.lift
      (Limits.pullback.fst X.obj.hom Y₁.obj.hom)
      (Limits.pullback.snd X.obj.hom Y₁.obj.hom ≫ f.left) (by simp only [Functor.id_obj,
        Functor.const_obj_obj, Over.mk_left, Over.mk_hom, Limits.pullback.condition, Category.assoc,
        Over.w])) (by simp only [Functor.id_obj, Functor.const_obj_obj, Over.mk_left, Over.mk_hom,
          Limits.limit.lift_π_assoc, Limits.PullbackCone.mk_pt, Limits.cospan_left,
          Limits.PullbackCone.mk_π_app])
  whiskerRight := by
    rintro X₁ X₂ f Y
    refine Over.homMk (CategoryTheory.Limits.pullback.lift
      (Limits.pullback.fst X₁.obj.hom Y.obj.hom ≫ f.left)
      (Limits.pullback.snd X₁.obj.hom Y.obj.hom) (by simp [Limits.pullback.condition])) (by simp)
  tensorUnit := {
    obj := .mk (𝟙 Spec R)
    property := by simp only [Pi.id_apply, Over.mk_left, Functor.id_obj, Functor.const_obj_obj,
      Over.mk_hom, IsVarietyHom.id]
  }
  associator := sorry
  leftUnitor := sorry
  rightUnitor := sorry

end AlgebraicGeometry
