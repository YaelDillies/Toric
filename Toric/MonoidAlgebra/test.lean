/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.Algebra.Category.Grp.Adjunctions
import Mathlib.Algebra.Category.Grp.EquivalenceGroupAddGroup
import Mathlib.Algebra.Category.Ring.Adjunctions
import Mathlib.AlgebraicGeometry.Limits
import Toric.Mathlib.Algebra.Category.Grp.Basic
import Toric.Mathlib.Algebra.Category.MonCat.Basic
import Toric.Mathlib.CategoryTheory.Monoidal.Cartesian.CommGrp_
import Toric.MvLaurentPolynomial
import Toric.GroupScheme.SpecGrpAlg
import Toric.MonoidAlgebra.TensorProduct
import Toric.Hopf.TensorProduct

universe v u

open CategoryTheory Limits Opposite


namespace AlgebraicGeometry.Scheme

-- attribute [local instance] ChosenFiniteProducts.ofFiniteProducts

noncomputable section

instance {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] :
    (Spec (.of S)).Over (Spec (.of R)) :=
  ⟨Spec.map (CommRingCat.ofHom (algebraMap R S))⟩

-- should we give `(OverClass.asOver (Spec (.of S)) (Spec (.of R)))` a name?
instance Mon_ClassOfBialgbra {R S : Type u} [CommRing R] [CommRing S] [Bialgebra R S] :
    Mon_Class (OverClass.asOver (Spec (.of S)) (Spec (.of R))) :=
  ((bialgSpec (.of R)).obj (op (.of R S))).instMon_ClassX

attribute [local instance] Functor.monoidalOfChosenFiniteProducts in
instance Mon_ClassOverMkPullbackSnd
    {X Y S : Scheme} (f : X ⟶ S) (g : Y ⟶ S) [Mon_Class (Over.mk f)] :
    Mon_Class (Over.mk (pullback.snd f g)) :=
  ((Over.pullback g).mapMon.obj (Mon_.mk' (Over.mk f))).instMon_ClassX

def Mon (S : Scheme.{max u v}) (M : Type v) [CommMonoid M] : Scheme :=
    pullback ((Spec (.of (MonoidAlgebra (ULift.{max u v} ℤ) M))) ↘ _)
      (specULiftZIsTerminal.from S)

instance (S : Scheme.{max u v}) (M : Type v) [CommMonoid M] : (Mon S M).Over S :=
  ⟨pullback.snd _ _⟩

instance (S : Scheme.{max u v}) (M : Type v) [CommMonoid M] :
    Mon_Class (OverClass.asOver (Mon S M) S) :=
  letI : Mon_Class (Over.mk (Spec (.of
    (MonoidAlgebra (ULift.{max u v} ℤ) M)) ↘ Spec (.of (ULift.{max u v} ℤ)))) := Mon_ClassOfBialgbra
  Mon_ClassOverMkPullbackSnd _ _

@[simp]
lemma preservesTerminalIso_pullback {R S : CommRingCat.{u}} (f : R ⟶ S) :
    (CartesianMonoidalCategory.preservesTerminalIso (Over.pullback (Spec.map f))) =
    Over.isoMk (asIso (pullback.snd (𝟙 _) (Spec.map f))) (by simp) := by
  ext1
  exact CartesianMonoidalCategory.toUnit_unique _ _

attribute [local instance] MonoidAlgebra.algebraMonoidAlgebra

@[simp]
lemma prodComparisonIso_algSpec_hom_left {R : CommRingCat.{u}} (A B : (CommAlgCat ↑R)ᵒᵖ) :
    (CartesianMonoidalCategory.prodComparisonIso (algSpec R) A B).hom.left =
      (pullbackSpecIso R A.unop B.unop).inv := rfl

@[simp]
lemma prodComparisonIso_algSpec_inv_left {R : CommRingCat.{u}} (A B : (CommAlgCat ↑R)ᵒᵖ) :
    (CartesianMonoidalCategory.prodComparisonIso (algSpec R) A B).inv.left =
      (pullbackSpecIso R A.unop B.unop).hom := by
  rw [← Iso.comp_inv_eq_id, ← prodComparisonIso_algSpec_hom_left, ← Over.comp_left,
    Iso.inv_hom_id, Over.id_left]

open CartesianMonoidalCategory in
@[simp]
lemma prodComparisonIso_pullback_Spec_hom_left {R S : CommRingCat.{u}} (f : R ⟶ S)
    (A B : Over (Spec R)) :
    (by exact (prodComparisonIso (Over.pullback (Spec.map f)) A B).inv.left) ≫
      pullback.fst (pullback.fst A.hom B.hom ≫ A.hom) (Spec.map f) ≫
        pullback.fst _ _ = pullback.fst (pullback.snd A.hom (Spec.map f))
          (pullback.snd B.hom (Spec.map f)) ≫ pullback.fst _ _ := by
  rw [← cancel_epi (prodComparisonIso (Over.pullback (Spec.map f)) A B).hom.left,
    Over.hom_left_inv_left_assoc]
  simp [CartesianMonoidalCategory.prodComparison]
  rfl

open CartesianMonoidalCategory in
@[simp]
lemma prodComparisonIso_pullback_Spec_inv_left_fst_fst' {R S : CommRingCat.{u}} (f : R ⟶ S)
    {A B : Scheme.{u}} (fA : A ⟶ Spec R) (fB : B ⟶ Spec R) :
    (by exact (prodComparisonIso (Over.pullback (Spec.map f)) (Over.mk fA) (Over.mk fB)).inv.left) ≫
      pullback.fst (pullback.fst fA fB ≫ fA) (Spec.map f) ≫
        pullback.fst _ _ = pullback.fst (pullback.snd fA (Spec.map f))
          (pullback.snd fB (Spec.map f)) ≫ pullback.fst _ _ :=
  prodComparisonIso_pullback_Spec_hom_left ..

open CartesianMonoidalCategory in
@[simp]
lemma prodComparisonIso_pullback_Spec_inv_left_fst_snd' {R S : CommRingCat.{u}} (f : R ⟶ S)
    {A B : Scheme.{u}} (fA : A ⟶ Spec R) (fB : B ⟶ Spec R) :
    (by exact (prodComparisonIso (Over.pullback (Spec.map f)) (Over.mk fA) (Over.mk fB)).inv.left) ≫
      pullback.fst (pullback.fst fA fB ≫ fA) (Spec.map f) ≫
        pullback.snd _ _ = pullback.snd _ _ ≫ pullback.fst _ _ := by
  rw [← cancel_epi (prodComparisonIso (Over.pullback (Spec.map f)) _ _).hom.left,
    Over.hom_left_inv_left_assoc]
  simp [CartesianMonoidalCategory.prodComparison]
  rfl

open CartesianMonoidalCategory in
@[simp]
lemma prodComparisonIso_pullback_Spec_inv_left_snd' {R S : CommRingCat.{u}} (f : R ⟶ S)
    {A B : Scheme.{u}} (fA : A ⟶ Spec R) (fB : B ⟶ Spec R) :
    (by exact (prodComparisonIso (Over.pullback (Spec.map f)) (Over.mk fA) (Over.mk fB)).inv.left) ≫
      pullback.snd (pullback.fst fA fB ≫ fA) (Spec.map f) =
        pullback.snd _ _ ≫ pullback.snd _ _ := by
  rw [← cancel_epi (prodComparisonIso (Over.pullback (Spec.map f)) _ _).hom.left,
    Over.hom_left_inv_left_assoc]
  simp [CartesianMonoidalCategory.prodComparison]

attribute [local instance] Over.cartesianMonoidalCategory in
open scoped MonoidalCategory in
@[reassoc (attr := simp)]
lemma CategoryTheory.Over.tensorHom_left_fst' {C : Type*} [Category C] [HasPullbacks C] {X : C}
    {S U : C} {R T : Over X} (fS : S ⟶ X) (fU : U ⟶ X) (f : R ⟶ Over.mk fS) (g : T ⟶ Over.mk fU) :
    (f ⊗ g).left ≫ pullback.fst fS fU = pullback.fst R.hom T.hom ≫ f.left :=
  CategoryTheory.Over.tensorHom_left_fst ..

attribute [local instance] Over.cartesianMonoidalCategory in
open scoped MonoidalCategory in
@[reassoc (attr := simp)]
lemma CategoryTheory.Over.tensorHom_left_snd' {C : Type*} [Category C] [HasPullbacks C] {X : C}
    {S U : C} {R T : Over X} (fS : S ⟶ X) (fU : U ⟶ X) (f : R ⟶ Over.mk fS) (g : T ⟶ Over.mk fU) :
    (f ⊗ g).left ≫ pullback.snd fS fU = pullback.snd R.hom T.hom ≫ g.left :=
  CategoryTheory.Over.tensorHom_left_snd ..


lemma TensorProduct.algebraMap_def {R S T : Type*}
    [CommSemiring R] [CommSemiring S] [CommSemiring T] [Algebra R S] [Algebra R T] :
  (algebraMap S (TensorProduct R S T)) = Algebra.TensorProduct.includeLeftRingHom := rfl

lemma preservesTerminalIso_algSpec (R : CommRingCat.{u}) :
  (CartesianMonoidalCategory.preservesTerminalIso (algSpec R)) =
    Over.isoMk (Iso.refl (Spec R)) (by dsimp; simp [MonoidalCategoryStruct.tensorUnit]) := by
  ext1; exact CartesianMonoidalCategory.toUnit_unique _ _

@[simp]
lemma preservesTerminalIso_algSpec_inv_left (R : CommRingCat.{u}) :
  (CartesianMonoidalCategory.preservesTerminalIso (algSpec R)).inv.left = 𝟙 (Spec R) := by
  simp [preservesTerminalIso_algSpec]

@[simp]
lemma AlgHomClass.toAlgHom_toRingHom {R A B : Type*} [CommSemiring R] [Semiring A]
    [Semiring B] [Algebra R A] [Algebra R B] {F : Type*} [FunLike F A B] [AlgHomClass F R A B]
    (f : F) : (RingHomClass.toRingHom (AlgHomClass.toAlgHom f)) = RingHomClass.toRingHom f := rfl

section

attribute [local instance] Functor.Monoidal.ofChosenFiniteProducts

local notation3:max R:max "[" M:max "]" => MonoidAlgebra R M

variable {R S : CommRingCat.{u}} (f : R ⟶ S) (M : CommMonCat.{u})

open MonoidalCategory MonoidAlgebra

abbrev specCommMonAlgPullbackObjXIso :
    ((specCommMonAlg R ⋙ (Over.pullback (Spec.map f)).mapMon).obj (.op M)).X ≅
      ((specCommMonAlg S).obj (.op M)).X :=
  letI := f.hom.toAlgebra
  let H := (CommRingCat.isPushout_of_isPushout R S R[M] S[M]).op.map Scheme.Spec
  Over.isoMk H.isoPullback.symm (by dsimp; simp; rfl)

lemma specCommMonAlgPullbackObjXIso_one :
    Mon_.one _ ≫ (specCommMonAlgPullbackObjXIso f M).hom = Mon_.one _ := by
  letI := f.hom.toAlgebra
  have h₁ := counitAlgHom_comp_mapRangeRingHom f.hom (M := M)
  have h₂ := (Bialgebra.counitAlgHom S S[M]).comp_algebraMap
  apply_fun (Spec.map <| CommRingCat.ofHom ·) at h₁ h₂
  simp only [AlgHom.toRingHom_eq_coe, CommRingCat.ofHom_comp, Spec.map_comp] at h₁ h₂
  ext
  apply ((CommRingCat.isPushout_of_isPushout R S R[M] S[M]).op.map Scheme.Spec).hom_ext <;>
    simp [Functor.Monoidal.ε_of_cartesianMonoidalCategory, RingHom.algebraMap_toAlgebra,
      AlgHom.toUnder, h₁, h₂]

@[reassoc]
lemma specCommMonAlgPullbackObjIso_mul_aux :
    (CartesianMonoidalCategory.prodComparisonIso (Over.pullback (Spec.map f)) _ _).inv.left ≫
      pullback.fst _ _ ≫ (pullbackSpecIso R R[M] R[M]).hom =
    ((specCommMonAlgPullbackObjXIso f M).hom ⊗ (specCommMonAlgPullbackObjXIso f M).hom).left ≫
      (pullbackSpecIso S _ _).hom ≫
        Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.mapRingHom f.hom _ _
          (mapRangeRingHom_comp_algebraMap f.hom (M := M))
          (mapRangeRingHom_comp_algebraMap f.hom (M := M)))) := by
  letI := f.hom.toAlgebra
  letI H := (CommRingCat.isPushout_of_isPushout R S R[M] S[M]).op.map Scheme.Spec
  letI e : ((specCommMonAlg R ⋙ (Over.pullback (Spec.map f)).mapMon).obj (.op M)).X ≅
    ((specCommMonAlg S).obj (.op M)).X := Over.isoMk H.isoPullback.symm (by dsimp; simp; rfl)
  letI hc := mapRangeRingHom_comp_algebraMap f.hom (M := M)
  have h₂ := Algebra.TensorProduct.mapRingHom_comp_includeLeftRingHom _ _ _ hc hc
  have h₃ := Algebra.TensorProduct.mapRingHom_comp_includeRight _ _ _ hc hc
  apply_fun (Spec.map <| CommRingCat.ofHom ·) at h₂ h₃
  simp only [AlgHom.toRingHom_eq_coe, CommRingCat.ofHom_comp, Spec.map_comp] at h₂ h₃
  rw [← Category.assoc, ← Iso.eq_comp_inv]
  dsimp
  ext <;> simp [h₂, h₃, e, RingHom.algebraMap_toAlgebra]

set_option maxHeartbeats 0 in
lemma specCommMonAlgPullbackObjXIso_mul :
    Mon_.mul _ ≫ (specCommMonAlgPullbackObjXIso f M).hom =
    ((specCommMonAlgPullbackObjXIso f M).hom ⊗ (specCommMonAlgPullbackObjXIso f M).hom) ≫
      Mon_.mul _ := by
  letI := f.hom.toAlgebra
  have h₃ := comulAlgHom_comp_mapRangeRingHom f.hom (M := M)
  have h₄ := (Bialgebra.comulAlgHom S S[M]).comp_algebraMap
  have h₅ := IsScalarTower.algebraMap_eq S S[M] (TensorProduct S S[M] S[M])
  apply_fun (Spec.map <| CommRingCat.ofHom ·) at h₃ h₄ h₅
  simp only [AlgHom.toRingHom_eq_coe, CommRingCat.ofHom_comp, Spec.map_comp] at h₃ h₄ h₅
  ext
  apply ((CommRingCat.isPushout_of_isPushout R S R[M] S[M]).op.map Scheme.Spec).hom_ext
  · simpa [Functor.Monoidal.μ_of_cartesianMonoidalCategory, RingHom.algebraMap_toAlgebra,
      AlgHom.toUnder, h₃, specCommMonAlgPullbackObjXIso] using
        specCommMonAlgPullbackObjIso_mul_aux_assoc f M
          (Spec.map (CommRingCat.ofHom (Bialgebra.comulAlgHom R R[M]).toRingHom))
  · simp [Functor.Monoidal.μ_of_cartesianMonoidalCategory, RingHom.algebraMap_toAlgebra,
      AlgHom.toUnder, h₄, h₅, TensorProduct.algebraMap_def, pullback.condition]

-- should we make something like `BialgHom.toRingHom`?
def specCommMonAlgPullback :
    specCommMonAlg R ⋙ (Over.pullback (Spec.map f)).mapMon ≅ specCommMonAlg S :=
  NatIso.ofComponents (fun M ↦ Mon_.mkIso (specCommMonAlgPullbackObjXIso f M.unop)
   (specCommMonAlgPullbackObjXIso_one f M.unop) (specCommMonAlgPullbackObjXIso_mul f M.unop))
  fun {M N} φ ↦ by
    letI := f.hom.toAlgebra
    letI H := (CommRingCat.isPushout_of_isPushout R S R[N.unop] S[N.unop]).op.map Scheme.Spec
    have h₁ : (mapRangeRingHom f.hom).comp (mapDomainBialgHom R φ.unop.hom) =
        (RingHomClass.toRingHom (mapDomainBialgHom S φ.unop.hom)).comp
          (mapRangeRingHom f.hom) := mapRangeRingHom_comp_mapDomainBialgHom _ _
    have h₂ := (AlgHomClass.toAlgHom (mapDomainBialgHom S φ.unop.hom)).comp_algebraMap
    apply_fun (Spec.map <| CommRingCat.ofHom ·) at h₁ h₂
    simp only [AlgHom.toRingHom_eq_coe, CommRingCat.ofHom_comp, Spec.map_comp] at h₁ h₂
    ext
    apply ((CommRingCat.isPushout_of_isPushout R S R[N.unop] S[N.unop]).op.map Scheme.Spec).hom_ext
    · simp [RingHom.algebraMap_toAlgebra,AlgHom.toUnder, Iso.eq_inv_comp, h₁]
    · simp [RingHom.algebraMap_toAlgebra, AlgHom.toUnder, Iso.eq_inv_comp, ← h₂]

end

section

attribute [local instance] Functor.Monoidal.ofChosenFiniteProducts

local notation3:max R:max "[" M:max "]" => MonoidAlgebra R M

variable {R S : CommRingCat.{u}} (f : R ⟶ S) (M : CommGrp.{u})

open MonoidalCategory MonoidAlgebra

/-- Given a natural isomorphism between `F ⋙ H` and `G ⋙ H` for a fully faithful functor `H`, we
can 'cancel' it to give a natural iso between `F` and `G`.
-/
noncomputable def _root_.CategoryTheory.Functor.FullyFaithful.cancelRight {C : Type*} [Category C]
  {D : Type*} [Category D] {E : Type*} [Category E] {F G : C ⥤ D} {H : D ⥤ E}
    (HH : H.FullyFaithful) (comp_iso : F ⋙ H ≅ G ⋙ H) : F ≅ G :=
  NatIso.ofComponents (fun X => HH.preimageIso (comp_iso.app X)) fun f =>
    HH.map_injective (by simpa using comp_iso.hom.naturality f)

-- should we make something like `BialgHom.toRingHom`?
def specCommGrpAlgPullback :
    specCommGrpAlg R ⋙ (Over.pullback (Spec.map f)).mapGrp ≅ specCommGrpAlg S :=
  (Grp_.fullyFaithfulForget₂Mon_ _).cancelRight
    (isoWhiskerLeft (forget₂ CommGrp CommMonCat).op (specCommMonAlgPullback f))

end

end

end AlgebraicGeometry.Scheme
