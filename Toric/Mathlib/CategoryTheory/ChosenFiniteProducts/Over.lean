/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.CategoryTheory.ChosenFiniteProducts

/-!
# This is https://github.com/leanprover-community/mathlib4/pull/21399
-/

namespace CategoryTheory.Over

open Limits

variable {C : Type*} [Category C] [HasPullbacks C]

/-- A choice of finite products of `Over X` given by `Limits.pullback`. -/
@[reducible]
noncomputable
def chosenFiniteProducts (X : C) : ChosenFiniteProducts (Over X) where
  product Y Z := ⟨BinaryFan.mk (P := Over.mk (pullback.snd Y.hom Z.hom ≫ Z.hom))
      (Over.homMk (pullback.fst Y.hom Z.hom) pullback.condition)
      (Over.homMk (pullback.snd Y.hom Z.hom) rfl),
    BinaryFan.isLimitMk
      (fun s ↦ Over.homMk (pullback.lift s.fst.left s.snd.left (s.fst.w.trans s.snd.w.symm))
        ((pullback.lift_snd_assoc _ _ _ _).trans (s.snd.w.trans (Category.comp_id _))))
      (fun s ↦ Over.OverMorphism.ext (pullback.lift_fst _ _ _))
      (fun s ↦ Over.OverMorphism.ext (pullback.lift_snd _ _ _)) fun s m e₁ e₂ ↦ by
      ext1
      apply pullback.hom_ext
      · simpa using congr(($e₁).left)
      · simpa using congr(($e₂).left)⟩
  terminal := ⟨asEmptyCone (Over.mk (𝟙 X)), IsTerminal.ofUniqueHom (fun Y ↦ Over.homMk Y.hom)
    fun Y m ↦ Over.OverMorphism.ext (by simpa using m.w)⟩

attribute [local instance] chosenFiniteProducts

open MonoidalCategory

variable {X : C}

@[ext]
lemma tensorObj_ext {R : C} {S T : Over X} (f₁ f₂ : R ⟶ (S ⊗ T).left)
    (e₁ : f₁ ≫ pullback.fst _ _ = f₂ ≫ pullback.fst _ _)
    (e₂ : f₁ ≫ pullback.snd _ _ = f₂ ≫ pullback.snd _ _) : f₁ = f₂ :=
  pullback.hom_ext e₁ e₂

@[simp]
lemma tensorObj_left (R S : Over X) : (R ⊗ S).left = Limits.pullback R.hom S.hom := rfl

@[simp]
lemma tensorObj_hom (R S : Over X) : (R ⊗ S).hom = pullback.snd R.hom S.hom ≫ S.hom := rfl

@[simp]
lemma tensorUnit_left : (𝟙_ (Over X)).left = X := rfl

@[simp]
lemma tensorUnit_hom : (𝟙_ (Over X)).hom = 𝟙 X := rfl

@[reassoc (attr := simp)]
lemma associator_hom_left_fst (R S T : Over X) :
    (α_ R S T).hom.left ≫ pullback.fst R.hom (pullback.snd _ _ ≫ T.hom) =
      pullback.fst _ _ ≫ pullback.fst _ _ :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma associator_hom_left_snd_fst (R S T : Over X) :
    (α_ R S T).hom.left ≫ pullback.snd _ (pullback.snd _ _ ≫ T.hom) ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ pullback.snd _ _ :=
  (pullback.lift_snd_assoc _ _ _ _).trans (pullback.lift_fst _ _ _)

@[reassoc (attr := simp)]
lemma associator_hom_left_snd_snd (R S T : Over X) :
    (α_ R S T).hom.left ≫ pullback.snd _ (pullback.snd _ _ ≫ T.hom) ≫ pullback.snd _ _ =
      pullback.snd _ _ :=
  (pullback.lift_snd_assoc _ _ _ _).trans (pullback.lift_snd _ _ _)

@[reassoc (attr := simp)]
lemma associator_inv_left_fst (R S T : Over X) :
    (α_ R S T).inv.left ≫ pullback.fst (pullback.snd _ _ ≫ _) _ ≫ pullback.fst _ _ =
    pullback.fst _ _ :=
  (pullback.lift_fst_assoc _ _ _ _).trans (pullback.lift_fst _ _ _)

@[reassoc (attr := simp)]
lemma associator_inv_left_fst_snd (R S T : Over X) :
    (α_ R S T).inv.left ≫ pullback.fst (pullback.snd _ _ ≫ _) _ ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ pullback.fst _ _ :=
  (pullback.lift_fst_assoc _ _ _ _).trans (pullback.lift_snd _ _ _)

@[reassoc (attr := simp)]
lemma associator_inv_left_snd (R S T : Over X) :
    (α_ R S T).inv.left ≫ pullback.snd (pullback.snd _ _ ≫ _) _ =
    pullback.snd _ _ ≫ pullback.snd _ _ :=
  pullback.lift_snd _ _ _

@[simp]
lemma leftUnitor_hom_left (Y : Over X) :
    (λ_ Y).hom.left = pullback.snd _ _ := rfl

@[reassoc (attr := simp)]
lemma leftUnitor_inv_left_fst (Y : Over X) :
    (λ_ Y).inv.left ≫ pullback.fst (𝟙 X) _ = Y.hom :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma leftUnitor_inv_left_snd (Y : Over X) :
    (λ_ Y).inv.left ≫ pullback.snd (𝟙 X) _ = 𝟙 Y.left :=
  pullback.lift_snd _ _ _

@[simp]
lemma rightUnitor_hom_left (Y : Over X) :
    (ρ_ Y).hom.left = pullback.fst _ (𝟙 X) := rfl

@[reassoc (attr := simp)]
lemma rightUnitor_inv_left_fst (Y : Over X) :
    (ρ_ Y).inv.left ≫ pullback.fst _ (𝟙 X) = 𝟙 _ :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma rightUnitor_inv_left_snd (Y : Over X) :
    (ρ_ Y).inv.left ≫ pullback.snd _ (𝟙 X) = Y.hom :=
  pullback.lift_snd _ _ _

lemma whiskerLeft_left {R S T : Over X} (f : S ⟶ T) :
    (R ◁ f).left = pullback.map _ _ _ _ (𝟙 _) f.left (𝟙 _) (by simp) (by simp) := rfl

@[reassoc (attr := simp)]
lemma whiskerLeft_left_fst {R S T : Over X} (f : S ⟶ T) :
    (R ◁ f).left ≫ pullback.fst _ _ = pullback.fst _ _ :=
  (pullback.lift_fst _ _ _).trans (Category.comp_id _)

@[reassoc (attr := simp)]
lemma whiskerLeft_left_snd {R S T : Over X} (f : S ⟶ T) :
    (R ◁ f).left ≫ pullback.snd _ _ = pullback.snd _ _ ≫ f.left :=
  pullback.lift_snd _ _ _

lemma whiskerRight_left {R S T : Over X} (f : S ⟶ T) :
    (f ▷ R).left = pullback.map _ _ _ _ f.left (𝟙 _) (𝟙 _) (by simp) (by simp) := rfl

@[reassoc (attr := simp)]
lemma whiskerRight_left_fst {R S T : Over X} (f : S ⟶ T) :
    (f ▷ R).left ≫ pullback.fst _ _ = pullback.fst _ _ ≫ f.left :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma whiskerRight_left_snd {R S T : Over X} (f : S ⟶ T) :
    (f ▷ R).left ≫ pullback.snd _ _ = pullback.snd _ _ :=
  (pullback.lift_snd _ _ _).trans (Category.comp_id _)

lemma tensorHom_left {R S T U : Over X} (f : R ⟶ S) (g : T ⟶ U) :
    (f ⊗ g).left = pullback.map _ _ _ _ f.left g.left (𝟙 _) (by simp) (by simp) := rfl

@[reassoc (attr := simp)]
lemma tensorHom_left_fst {R S T U : Over X} (f : R ⟶ S) (g : T ⟶ U) :
    (f ⊗ g).left ≫ pullback.fst _ _ = pullback.fst _ _ ≫ f.left :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma tensorHom_left_snd {R S T U : Over X} (f : R ⟶ S) (g : T ⟶ U) :
    (f ⊗ g).left ≫ pullback.snd _ _ = pullback.snd _ _ ≫ g.left :=
  pullback.lift_snd _ _ _

@[simp]
lemma braiding_hom_left {R S : Over X} :
    (β_ R S).hom.left = (pullbackSymmetry _ _).hom := rfl

@[simp]
lemma braiding_inv_left {R S : Over X} :
    (β_ R S).inv.left = (pullbackSymmetry _ _).hom := rfl

end CategoryTheory.Over
