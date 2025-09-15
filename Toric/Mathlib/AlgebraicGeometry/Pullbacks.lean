import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.CategoryTheory.Monoidal.CommMon_
import Mathlib.CategoryTheory.Monoidal.Grp_
import Toric.Mathlib.RingTheory.TensorProduct.Basic

noncomputable section

open CategoryTheory CartesianMonoidalCategory Limits

namespace AlgebraicGeometry.Scheme
universe u
variable {M S T : Scheme.{u}} [M.Over S] {f : T ⟶ S}

instance : (Over.pullback f).Braided := .ofChosenFiniteProducts _

@[simps]
instance canonicallyOverPullback : (pullback (M ↘ S) f).CanonicallyOver T where
  hom := pullback.snd (M ↘ S) f

@[simps! -isSimp mul one]
instance monObjAsOverPullback [MonObj (asOver M S)] : MonObj (asOver (pullback (M ↘ S) f) T) :=
  ((Over.pullback f).mapMon.obj <| .mk <| asOver M S).mon

instance isCommMonObj_asOver_pullback [MonObj (asOver M S)] [IsCommMonObj (asOver M S)] :
    IsCommMonObj (asOver (pullback (M ↘ S) f) T) :=
  ((Over.pullback f).mapCommMon.obj <| .mk <| asOver M S).comm

instance GrpObjAsOverPullback [GrpObj (asOver M S)] :
    GrpObj (asOver (pullback (M ↘ S) f) T) :=
  ((Over.pullback f).mapGrp.obj <| .mk <| asOver M S).grp

instance : (pullback.fst (M ↘ S) (𝟙 S)).IsOver S := ⟨(pullback.condition).trans (by simp)⟩

@[simp]
lemma η_pullback_left :
  ((Functor.OplaxMonoidal.η (Over.pullback f))).left = (pullback.snd (𝟙 _) f) := rfl

@[simp]
lemma ε_pullback_left :
    ((Functor.LaxMonoidal.ε (Over.pullback f))).left = inv (pullback.snd (𝟙 _) f) := by
  apply IsIso.eq_inv_of_hom_inv_id
  rw [← η_pullback_left, ← Over.comp_left, Functor.Monoidal.η_ε, Over.id_left]

lemma μ_pullback_left_fst_fst (X Y : Over S) :
    ((Functor.LaxMonoidal.μ (Over.pullback f) X Y)).left ≫
      pullback.fst _ _ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ pullback.fst _ _ := by
  rw [Functor.Monoidal.μ_of_cartesianMonoidalCategory,
    ← cancel_epi (prodComparisonIso (Over.pullback f) X Y).hom.left, ← Over.comp_left_assoc,
    Iso.hom_inv_id]
  simp [CartesianMonoidalCategory.prodComparison]
  rfl

lemma μ_pullback_left_fst_snd (X Y : Over S) :
    ((Functor.LaxMonoidal.μ (Over.pullback f) X Y)).left ≫
      pullback.fst _ _ ≫ pullback.snd _ _ = pullback.snd _ _ ≫ pullback.fst _ _ := by
  rw [Functor.Monoidal.μ_of_cartesianMonoidalCategory,
    ← cancel_epi (prodComparisonIso (Over.pullback f) X Y).hom.left,
    ← Over.comp_left_assoc, Iso.hom_inv_id]
  simp [CartesianMonoidalCategory.prodComparison]
  rfl

lemma μ_pullback_left_snd (X Y : Over S) :
    ((Functor.LaxMonoidal.μ (Over.pullback f) X Y)).left ≫
      pullback.snd _ _ = pullback.snd _ _ ≫ pullback.snd _ _ := by
  rw [Functor.Monoidal.μ_of_cartesianMonoidalCategory,
    ← cancel_epi (prodComparisonIso (Over.pullback f) X Y).hom.left,
    ← Over.comp_left_assoc, Iso.hom_inv_id]
  simp [CartesianMonoidalCategory.prodComparison]

@[simp]
lemma μ_pullback_left_fst_fst' {X Y : Scheme} (g₁ : X ⟶ S) (g₂ : Y ⟶ S) :
    ((Functor.LaxMonoidal.μ (Over.pullback f) (.mk g₁) (.mk g₂))).left ≫
      pullback.fst (pullback.fst g₁ g₂ ≫ g₁) f ≫ pullback.fst g₁ g₂ =
        pullback.fst _ _ ≫ pullback.fst _ _ :=
  μ_pullback_left_fst_fst ..

@[simp]
lemma μ_pullback_left_fst_snd' {X Y : Scheme} (g₁ : X ⟶ S) (g₂ : Y ⟶ S) :
    ((Functor.LaxMonoidal.μ (Over.pullback f) (.mk g₁) (.mk g₂))).left ≫
      pullback.fst (pullback.fst g₁ g₂ ≫ g₁) f ≫ pullback.snd g₁ g₂ =
        pullback.snd _ _ ≫ pullback.fst _ _ :=
  μ_pullback_left_fst_snd ..

@[simp]
lemma μ_pullback_left_snd' {X Y : Scheme} (g₁ : X ⟶ S) (g₂ : Y ⟶ S) :
    ((Functor.LaxMonoidal.μ (Over.pullback f) (.mk g₁) (.mk g₂))).left ≫
      pullback.snd (pullback.fst g₁ g₂ ≫ g₁) f =
        pullback.snd _ _ ≫ pullback.snd _ _ :=
  μ_pullback_left_snd ..

attribute [local simp] monObjAsOverPullback_one in
instance isMon_hom_fst_id_right [MonObj (asOver M S)] :
    IsMon_Hom ((pullback.fst (M ↘ S) (𝟙 S)).asOver S) where
  one_hom := by ext; simp [monObjAsOverPullback_one]
  mul_hom := by
    ext
    dsimp [monObjAsOverPullback_mul]
    simp only [Category.assoc, limit.lift_π, PullbackCone.mk_pt, PullbackCone.mk_π_app]
    simp only [← Category.assoc]
    congr 1
    ext <;> simp [OverClass.asOver]

@[simp]
lemma preservesTerminalIso_pullback {R S : CommRingCat.{u}} (f : R ⟶ S) :
    (preservesTerminalIso (Over.pullback (Spec.map f))) =
      Over.isoMk (asIso (pullback.snd (𝟙 _) (Spec.map f))) (by simp) := by
  ext1; exact toUnit_unique _ _

@[simp]
lemma prodComparisonIso_pullback_Spec_inv_left_fst_fst {R S : CommRingCat.{u}} (f : R ⟶ S)
    (A B : Over (Spec R)) :
    (prodComparisonIso (Over.pullback (Spec.map f)) A B).inv.left ≫
      pullback.fst (pullback.fst A.hom B.hom ≫ A.hom) (Spec.map f) ≫
        pullback.fst _ _ = pullback.fst (pullback.snd A.hom (Spec.map f))
          (pullback.snd B.hom (Spec.map f)) ≫ pullback.fst _ _ := by
  rw [← cancel_epi (prodComparisonIso (Over.pullback (Spec.map f)) A B).hom.left,
    Over.hom_left_inv_left_assoc]
  simp [CartesianMonoidalCategory.prodComparison]
  rfl

@[simp]
lemma prodComparisonIso_pullback_Spec_inv_left_fst_fst' {R S : CommRingCat.{u}} (f : R ⟶ S)
    {A B : Scheme.{u}} (fA : A ⟶ Spec R) (fB : B ⟶ Spec R) :
    (prodComparisonIso (Over.pullback (Spec.map f)) (Over.mk fA) (Over.mk fB)).inv.left ≫
      pullback.fst (pullback.fst fA fB ≫ fA) (Spec.map f) ≫
        pullback.fst _ _ = pullback.fst (pullback.snd fA (Spec.map f))
          (pullback.snd fB (Spec.map f)) ≫ pullback.fst _ _ :=
  prodComparisonIso_pullback_Spec_inv_left_fst_fst ..

@[simp]
lemma prodComparisonIso_pullback_Spec_inv_left_fst_snd' {R S : CommRingCat.{u}} (f : R ⟶ S)
    {A B : Scheme.{u}} (fA : A ⟶ Spec R) (fB : B ⟶ Spec R) :
    (prodComparisonIso (Over.pullback (Spec.map f)) (Over.mk fA) (Over.mk fB)).inv.left ≫
      pullback.fst (pullback.fst fA fB ≫ fA) (Spec.map f) ≫
        pullback.snd _ _ = pullback.snd _ _ ≫ pullback.fst _ _ := by
  rw [← cancel_epi (prodComparisonIso (Over.pullback (Spec.map f)) _ _).hom.left,
    Over.hom_left_inv_left_assoc]
  simp [CartesianMonoidalCategory.prodComparison]
  rfl

@[simp]
lemma prodComparisonIso_pullback_Spec_inv_left_snd' {R S : CommRingCat.{u}} (f : R ⟶ S)
    {A B : Scheme.{u}} (fA : A ⟶ Spec R) (fB : B ⟶ Spec R) :
    (by exact (prodComparisonIso (Over.pullback (Spec.map f)) (Over.mk fA) (Over.mk fB)).inv.left) ≫
      pullback.snd (pullback.fst fA fB ≫ fA) (Spec.map f) =
        pullback.snd _ _ ≫ pullback.snd _ _ := by
  rw [← cancel_epi (prodComparisonIso (Over.pullback (Spec.map f)) _ _).hom.left,
    Over.hom_left_inv_left_assoc]
  simp [CartesianMonoidalCategory.prodComparison]

@[reassoc (attr := simp)]
lemma pullbackSpecIso_hom_base (R S T : Type u) [CommRing R] [CommRing S] [CommRing T] [Algebra R S]
    [Algebra R T] :
    (pullbackSpecIso R S T).hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R _)) =
      pullback.fst _ _ ≫ Spec.map (CommRingCat.ofHom (algebraMap _ _)) := by
  simp [← Iso.eq_inv_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    ← Algebra.TensorProduct.algebraMap_def, ← IsScalarTower.algebraMap_eq]

@[reassoc (attr := simp)]
lemma pullbackSpecIso_hom_fst' (R S T : Type u) [CommRing R] [CommRing S] [CommRing T] [Algebra R S]
    [Algebra R T] :
    (pullbackSpecIso R S T).hom ≫ Spec.map (CommRingCat.ofHom (algebraMap S _)) =
      pullback.fst _ _ := by
  simp [← Iso.eq_inv_comp, pullbackSpecIso_inv_fst, ← Algebra.TensorProduct.algebraMap_def]

@[reassoc]
lemma pullbackSpecIso_inv_fst' (R S T : Type u) [CommRing R] [CommRing S] [CommRing T] [Algebra R S]
    [Algebra R T] :
    (pullbackSpecIso R S T).inv ≫ pullback.fst _ _ =
    Spec.map (CommRingCat.ofHom (algebraMap S _)) := by
  simp [← cancel_epi (pullbackSpecIso R S T).hom]

end AlgebraicGeometry.Scheme
