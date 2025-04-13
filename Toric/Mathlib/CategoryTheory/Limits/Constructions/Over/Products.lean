/-
Copyright (c) 2018 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Reid Barton, Bhavik Mehta
-/
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.PullbackCone
import Toric.Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts

/-!
# Products in the over category

Shows that products in the over category can be derived from wide pullbacks in the base category.
The main result is `over_product_of_widePullback`, which says that if `C` has `J`-indexed wide
pullbacks, then `Over B` has `J`-indexed products.
-/


universe w v u -- morphism levels before object levels. See note [category_theory universes].

open CategoryTheory CategoryTheory.Limits

variable {J : Type w}
variable {C : Type u} [Category.{v} C]
variable {X Y Z : C}

/-!
## Binary products

One could have used the following but it gives worse defeqs.
`(Cones.postcomposeEquivalence (diagramIsoCospan _).symm).trans (conesEquiv _ (pair Y Z))`
-/

namespace CategoryTheory.Limits
section Under
variable {f : X ⟶ Y} {g : X ⟶ Z}

/-- Pushout cocones from `X` are the same thing as binary cofans in `Under X`. -/
@[simps]
def pushoutCoconeEquivBinaryCofan : PushoutCocone f g ≌ BinaryCofan (Under.mk f) (.mk g) where
  functor.obj c := .mk (Under.homMk (U := .mk f) (V := .mk (f ≫ c.inl)) c.inl rfl)
      (Under.homMk (U := .mk g) (V := .mk (f ≫ c.inl)) c.inr c.condition.symm)
  functor.map {c₁ c₂} a := { hom := Under.homMk a.hom, w := by rintro (_|_) <;> aesop_cat }
  inverse.obj c := .mk c.inl.right c.inr.right (c.inl.w.symm.trans c.inr.w)
  inverse.map {c₁ c₂} a := {
    hom := a.hom.right
    w := by rintro (_|_|_) <;> dsimp <;> simp [← Under.comp_right]
  }
  unitIso := NatIso.ofComponents (fun c ↦ c.eta) (fun f ↦ by ext; dsimp; simp)
  counitIso := NatIso.ofComponents (fun X ↦ BinaryCofan.ext (Under.isoMk (.refl _)
    (by dsimp; simpa using X.inl.w.symm)) (by ext; dsimp; simp) (by ext; dsimp; simp))
    (by intros; ext; dsimp; simp)
  functor_unitIso_comp c := by ext; dsimp; simp

/-- A pushout cocone from `X` is a colimit if its corresponding binary cofan in `Under X` is a
colimit. -/
-- `IsColimit.ofCoconeEquiv` isn't used here because the lift it defines is `pushout.desc ≫ 𝟙 _`.
@[simps!]
def IsColimit.pushoutCoconeEquivBinaryCofan {c : PushoutCocone f g} (hc : IsColimit c) :
    IsColimit <| pushoutCoconeEquivBinaryCofan.functor.obj c :=
  BinaryCofan.isColimitMk
    (fun s ↦ Under.homMk
      (hc.desc (PushoutCocone.mk s.inl.right s.inr.right (s.inl.w.symm.trans s.inr.w))) <| by
        simpa using s.inl.w.symm)
    (fun s ↦ Under.UnderMorphism.ext (hc.fac _ _)) (fun s ↦ Under.UnderMorphism.ext (hc.fac _ _))
      fun s m e₁ e₂ ↦ by
    ext1
    refine PushoutCocone.IsColimit.hom_ext hc ?_ ?_
    · simpa using congr(($e₁).right)
    · simpa using congr(($e₂).right)

end Under

section Over
variable {f : Y ⟶ X} {g : Z ⟶ X} {c : PullbackCone f g}

/-- Pullback cones to `X` are the same thing as binary fans in `Over X`. -/
@[simps]
def pullbackConeEquivBinaryFan : PullbackCone f g ≌ BinaryFan (Over.mk f) (.mk g) where
  functor.obj c := .mk (Over.homMk (U := .mk (c.fst ≫ f)) (V := .mk f) c.fst rfl)
      (Over.homMk (U := .mk (c.fst ≫ f)) (V := .mk g) c.snd c.condition.symm)
  functor.map {c₁ c₂} a := { hom := Over.homMk a.hom, w := by rintro (_|_) <;> aesop_cat }
  inverse.obj c := PullbackCone.mk c.fst.left c.snd.left (c.fst.w.trans c.snd.w.symm)
  inverse.map {c₁ c₂} a := {
    hom := a.hom.left
    w := by rintro (_|_|_) <;> simp [← Over.comp_left_assoc, ← Over.comp_left]
  }
  unitIso := NatIso.ofComponents (fun c ↦ c.eta) (by intros; ext; dsimp; simp)
  counitIso := NatIso.ofComponents (fun X ↦ BinaryFan.ext (Over.isoMk (Iso.refl _)
    (by simpa using X.fst.w.symm)) (by ext; dsimp; simp) (by ext; dsimp; simp))
    (by intros; ext; dsimp; simp [BinaryFan.ext])
  functor_unitIso_comp c := by ext; dsimp; simp [BinaryFan.ext]

/-- A pullback cone to `X` is a limit if its corresponding binary fan in `Over X` is a limit. -/
-- `IsLimit.ofConeEquiv` isn't used here because the lift it defines is `𝟙 _ ≫ pullback.lift`.
@[simps!]
def IsLimit.pullbackConeEquivBinaryFan {c : PullbackCone f g} (hc : IsLimit c) :
    IsLimit <| pullbackConeEquivBinaryFan.functor.obj c :=
  BinaryFan.isLimitMk
    (fun s ↦ Over.homMk
      (hc.lift (PullbackCone.mk s.fst.left s.snd.left (s.fst.w.trans s.snd.w.symm))) <| by
        simpa using s.fst.w)
    (fun s ↦ Over.OverMorphism.ext (hc.fac _ _)) (fun s ↦ Over.OverMorphism.ext (hc.fac _ _))
      fun s m e₁ e₂ ↦ by
    ext1
    apply PullbackCone.IsLimit.hom_ext hc
    · simpa using congr(($e₁).left)
    · simpa using congr(($e₂).left)

end Over
end Limits
end CategoryTheory
