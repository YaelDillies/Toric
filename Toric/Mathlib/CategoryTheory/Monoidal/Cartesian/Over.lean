import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Comma.Over.Pullback
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import Mathlib.CategoryTheory.Monoidal.CommMon_
import Mathlib.CategoryTheory.Monoidal.Grp_

public noncomputable section

namespace CategoryTheory.Over

open Functor Limits CartesianMonoidalCategory

variable {C : Type*} [Category C] [HasPullbacks C]

attribute [local instance] cartesianMonoidalCategory

attribute [local instance] braidedCategory

open MonoidalCategory

variable {X : C} {A B R S Y Z : C} {f : R ⟶ X} {g : S ⟶ X}

instance : (Over.pullback f).Braided := .ofChosenFiniteProducts _

@[simp]
lemma η_pullback_left : (OplaxMonoidal.η (Over.pullback f)).left = (pullback.snd (𝟙 _) f) := rfl

@[simp]
lemma ε_pullback_left : (LaxMonoidal.ε (Over.pullback f)).left = inv (pullback.snd (𝟙 _) f) := by
  apply IsIso.eq_inv_of_hom_inv_id
  rw [← η_pullback_left, ← Over.comp_left, Monoidal.η_ε, Over.id_left]

lemma μ_pullback_left_fst_fst (R S : Over X) :
    (LaxMonoidal.μ (Over.pullback f) R S).left ≫
      pullback.fst _ _ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ pullback.fst _ _ := by
  rw [Monoidal.μ_of_cartesianMonoidalCategory,
    ← cancel_epi (prodComparisonIso (Over.pullback f) R S).hom.left, ← Over.comp_left_assoc,
    Iso.hom_inv_id]
  simp [CartesianMonoidalCategory.prodComparison, fst]

lemma μ_pullback_left_fst_snd (R S : Over X) :
    (LaxMonoidal.μ (Over.pullback f) R S).left ≫
      pullback.fst _ _ ≫ pullback.snd _ _ = pullback.snd _ _ ≫ pullback.fst _ _ := by
  rw [Monoidal.μ_of_cartesianMonoidalCategory,
    ← cancel_epi (prodComparisonIso (Over.pullback f) R S).hom.left,
    ← Over.comp_left_assoc, Iso.hom_inv_id]
  simp [CartesianMonoidalCategory.prodComparison, snd]

lemma μ_pullback_left_snd (R S : Over X) :
    (LaxMonoidal.μ (Over.pullback f) R S).left ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ pullback.snd _ _ := by
  rw [Monoidal.μ_of_cartesianMonoidalCategory,
    ← cancel_epi (prodComparisonIso (Over.pullback f) R S).hom.left,
    ← Over.comp_left_assoc, Iso.hom_inv_id]
  simp [CartesianMonoidalCategory.prodComparison]

@[simp]
lemma μ_pullback_left_fst_fst' (g₁ : Y ⟶ X) (g₂ : Z ⟶ X) :
    (LaxMonoidal.μ (Over.pullback f) (.mk g₁) (.mk g₂)).left ≫
      pullback.fst (pullback.fst g₁ g₂ ≫ g₁) f ≫ pullback.fst g₁ g₂ =
        pullback.fst _ _ ≫ pullback.fst _ _ :=
  μ_pullback_left_fst_fst ..

@[simp]
lemma μ_pullback_left_fst_snd' (g₁ : Y ⟶ X) (g₂ : Z ⟶ X) :
    (LaxMonoidal.μ (Over.pullback f) (.mk g₁) (.mk g₂)).left ≫
      pullback.fst (pullback.fst g₁ g₂ ≫ g₁) f ≫ pullback.snd g₁ g₂ =
        pullback.snd _ _ ≫ pullback.fst _ _ :=
  μ_pullback_left_fst_snd ..

@[simp]
lemma μ_pullback_left_snd' (g₁ : Y ⟶ X) (g₂ : Z ⟶ X) :
    (LaxMonoidal.μ (Over.pullback f) (.mk g₁) (.mk g₂)).left ≫
      pullback.snd (pullback.fst g₁ g₂ ≫ g₁) f =
        pullback.snd _ _ ≫ pullback.snd _ _ := μ_pullback_left_snd ..

@[simp]
lemma preservesTerminalIso_pullback (f : R ⟶ S) :
    preservesTerminalIso (Over.pullback f) =
      Over.isoMk (asIso (pullback.snd (𝟙 _) f)) (by simp) := by
  ext1; exact toUnit_unique _ _

@[simp]
lemma prodComparisonIso_pullback_inv_left_fst_fst (f : X ⟶ Y) (A B : Over Y) :
    (prodComparisonIso (Over.pullback f) A B).inv.left ≫
      pullback.fst (pullback.fst A.hom B.hom ≫ A.hom) f ≫ pullback.fst _ _ =
        pullback.fst (pullback.snd A.hom f) (pullback.snd B.hom f) ≫ pullback.fst _ _ := by
  rw [← cancel_epi (prodComparisonIso (Over.pullback f) A B).hom.left,
    Over.hom_left_inv_left_assoc]
  simp [CartesianMonoidalCategory.prodComparison, fst]

@[simp]
lemma prodComparisonIso_pullback_Spec_inv_left_fst_fst' (f : X ⟶ Y) (gA : A ⟶ Y) (gB : B ⟶ Y) :
    (prodComparisonIso (Over.pullback f) (.mk gA) (.mk gB)).inv.left ≫
      pullback.fst (pullback.fst gA gB ≫ gA) f ≫ pullback.fst _ _ =
        pullback.fst (pullback.snd gA f) (pullback.snd gB f) ≫ pullback.fst _ _ :=
  prodComparisonIso_pullback_inv_left_fst_fst ..

@[simp]
lemma prodComparisonIso_pullback_inv_left_fst_snd' (f : X ⟶ Y) (gA : A ⟶ Y) (gB : B ⟶ Y) :
    (prodComparisonIso (Over.pullback f) (.mk gA) (.mk gB)).inv.left ≫
      pullback.fst (pullback.fst gA gB ≫ gA) f ≫ pullback.snd _ _ =
        pullback.snd _ _ ≫ pullback.fst _ _ := by
  rw [← cancel_epi (prodComparisonIso (Over.pullback f) _ _).hom.left,
    Over.hom_left_inv_left_assoc]
  simp [CartesianMonoidalCategory.prodComparison, snd]

@[simp]
lemma prodComparisonIso_pullback_inv_left_snd' (f : X ⟶ Y) (gA : A ⟶ Y) (gB : B ⟶ Y) :
    (prodComparisonIso (Over.pullback f) (.mk gA) (.mk gB)).inv.left ≫
      pullback.snd (pullback.fst gA gB ≫ gA) f = pullback.snd _ _ ≫ pullback.snd _ _ := by
  rw [← cancel_epi (prodComparisonIso (Over.pullback f) _ _).hom.left,
    Over.hom_left_inv_left_assoc]
  simp [CartesianMonoidalCategory.prodComparison]

/-- The pullback of a monoid object is a monoid object. -/
@[simps! -isSimp mul one]
abbrev monObjMkPullbackSnd [MonObj (Over.mk f)] : MonObj (Over.mk <| pullback.snd f g) :=
  ((Over.pullback g).mapMon.obj <| .mk <| .mk f).mon

attribute [local instance] monObjMkPullbackSnd

instance isCommMonObj_mk_pullbackSnd [MonObj (Over.mk f)] [IsCommMonObj (Over.mk f)] :
    IsCommMonObj (Over.mk <| pullback.snd f g) :=
  ((Over.pullback g).mapCommMon.obj <| .mk <| .mk f).comm

/-- The pullback of a monoid object is a monoid object. -/
@[simps! -isSimp mul one]
abbrev grpObjMkPullbackSnd [GrpObj (Over.mk f)] : GrpObj (Over.mk (pullback.snd f g)) :=
  ((Over.pullback g).mapGrp.obj <| .mk <| .mk f).grp

attribute [local simp] monObjMkPullbackSnd_one in
instance isMonHom_pullbackFst_id_right [MonObj (Over.mk f)] :
    IsMonHom <| Over.homMk (U := Over.mk <| pullback.snd f (𝟙 X)) (V := Over.mk f)
      (pullback.fst f (𝟙 X)) (pullback.condition.trans <| by simp) where
  mul_hom := by
    ext
    dsimp [monObjMkPullbackSnd_mul]
    simp only [Category.assoc, limit.lift_π, PullbackCone.mk_pt, PullbackCone.mk_π_app]
    simp only [← Category.assoc]
    congr 1
    ext <;> simp

end CategoryTheory.Over
