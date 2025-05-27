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

local notation3:max R:max "[" M:max "]" => MonoidAlgebra R M

set_option maxHeartbeats 0 in
attribute [local instance] Functor.Monoidal.ofChosenFiniteProducts in
def foo {R S : CommRingCat.{u}} (f : R ⟶ S) :
    specCommMonAlg R ⋙ (Over.pullback (Spec.map f)).mapMon ≅ specCommMonAlg S :=
  NatIso.ofComponents (fun M ↦ Mon_.mkIso (Over.isoMk (by
    letI := f.hom.toAlgebra
    exact ((CommRingCat.isPushout_of_isPushout R S R[M.unop]
      (S[M.unop])).op.map Scheme.Spec).isoPullback.symm) (by dsimp; simp; rfl)) /- (by
    ext
    dsimp
    simp only [Functor.Monoidal.ε_of_cartesianMonoidalCategory, Functor.comp_obj,
      Equivalence.op_functor, Functor.op_obj, commAlgCatEquivUnder_functor_obj,
      Over.opEquivOpUnder_inverse_obj, Functor.id_obj, Functor.const_obj_obj,
      CommRingCat.mkUnder_hom, Over.post_obj, Spec_obj, Over.mk_left, Over.mk_hom, Spec_map,
      Quiver.Hom.unop_op, Category.assoc]
    rw [← Category.assoc, Iso.comp_inv_eq]
    have H (R : CommRingCat.{u}) : (CartesianMonoidalCategory.preservesTerminalIso (algSpec R)) =
      Over.isoMk (Iso.refl (Spec R)) (by dsimp; simp [MonoidalCategoryStruct.tensorUnit]) := by
      ext1; exact CartesianMonoidalCategory.toUnit_unique _ _
    letI := f.hom.toAlgebra
    ext
    · simp only [CommRingCat.mkUnder, Under.mk_right, preservesTerminalIso_pullback,
        Over.pullback_obj_left, Over.tensorUnit_left, Over.tensorUnit_hom, Over.isoMk_inv_left,
        asIso_inv, RingHom.algebraMap_toAlgebra, H, Functor.comp_obj, Equivalence.op_functor,
        Functor.op_obj, commAlgCatEquivUnder_functor_obj, Over.opEquivOpUnder_inverse_obj,
        Functor.id_obj, Functor.const_obj_obj, Under.mk_hom, Over.post_obj, Spec_obj,
        Over.mk_left, Over.mk_hom, Spec_map, Quiver.Hom.unop_op, Iso.refl_inv, Category.id_comp,
        Category.assoc, limit.lift_π, Functor.CoreMonoidal.toMonoidal_toLaxMonoidal, Iso.refl_hom,
        Algebra.id.map_eq_id, CommRingCat.ofHom_id, id_eq, PullbackCone.mk_pt,
        PullbackCone.mk_π_app, pullback_inv_snd_fst_of_left_isIso_assoc, IsIso.inv_id, ←
        Spec.map_comp, CommRingCat.ofHom_hom, IsPullback.isoPullback_hom_fst]
      congr 1
      ext1
      apply RingHom.coe_addMonoidHom_injective
      apply Finsupp.addHom_ext
      intro m r
      show f (Finsupp.lsum R _ (Finsupp.single _ _)) = Finsupp.lsum S _
        (MonoidAlgebra.lift R M.unop (S[M])
          (MonoidAlgebra.of S M.unop) _)
      simp [Algebra.smul_def, RingHom.algebraMap_toAlgebra]
    · simp only [CommRingCat.mkUnder, Under.mk_right, preservesTerminalIso_pullback,
        Over.pullback_obj_left, Over.tensorUnit_left, Over.tensorUnit_hom, Over.isoMk_inv_left,
        asIso_inv, RingHom.algebraMap_toAlgebra, H, Functor.comp_obj, Equivalence.op_functor,
        Functor.op_obj, commAlgCatEquivUnder_functor_obj, Over.opEquivOpUnder_inverse_obj,
        Functor.id_obj, Functor.const_obj_obj, Under.mk_hom, Over.post_obj, Spec_obj,
        Over.mk_left, Over.mk_hom, Spec_map, Quiver.Hom.unop_op, Iso.refl_inv, Category.id_comp,
        Category.assoc, limit.lift_π, Functor.CoreMonoidal.toMonoidal_toLaxMonoidal, Iso.refl_hom,
        Algebra.id.map_eq_id, CommRingCat.ofHom_id, id_eq, PullbackCone.mk_pt,
        PullbackCone.mk_π_app, IsIso.inv_hom_id, CommRingCat.ofHom_hom,
        IsPullback.isoPullback_hom_snd, ← Spec.map_comp, ← Spec.map_id]
      congr 1
      ext x
      show x = Finsupp.lsum R _ (Finsupp.single _ _)
      simp) -/ sorry (by
    obtain ⟨M⟩ := M
    letI := f.hom.toAlgebra
    let H := (CommRingCat.isPushout_of_isPushout R S R[M] S[M]).op.map Scheme.Spec
    letI e : ((specCommMonAlg R ⋙ (Over.pullback (Spec.map f)).mapMon).obj (.op M)).X ≅
      ((specCommMonAlg S).obj (.op M)).X := Over.isoMk H.isoPullback.symm (by dsimp; simp; rfl)
    have hc : (MonoidAlgebra.mapRangeRingHom f.hom).comp (algebraMap R R[M]) =
      (algebraMap S S[M]).comp f.hom := by ext; simp
    have h₁ := congr(Spec.map (CommRingCat.ofHom
      $(comulAlgHom_comp_mapRangeRingHom f.hom (M := M))))
    have h₂ := congr(Spec.map (CommRingCat.ofHom
      $(Algebra.TensorProduct.actualMap_comp_includeLeftRingHom _ _ _ hc hc)))
    have h₃ := congr(Spec.map (CommRingCat.ofHom
      $(Algebra.TensorProduct.actualMap_comp_includeRight _ _ _ hc hc)))
    have h₄ := congr(Spec.map (CommRingCat.ofHom
      $((Bialgebra.comulAlgHom S S[M]).comp_algebraMap)))
    have h₅ := congr(Spec.map (CommRingCat.ofHom
      $(IsScalarTower.algebraMap_eq S S[M] (TensorProduct S S[M] S[M]))))
    simp only [AlgHom.toRingHom_eq_coe, CommRingCat.ofHom_comp, Spec.map_comp] at h₁ h₂ h₃ h₄ h₅
    have goal :
      (CartesianMonoidalCategory.prodComparisonIso (Over.pullback (Spec.map f)) _ _).inv.left ≫
          pullback.fst _ _ ≫ (pullbackSpecIso R R[M] R[M]).hom =
      ((MonoidalCategoryStruct.tensorHom e.hom e.hom).left ≫ (pullbackSpecIso S _ _).hom) ≫
        Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.actualMap f.hom _ _ hc hc)) := by
      rw [← Category.assoc, ← Iso.eq_comp_inv]
      dsimp
      ext <;> simp [h₂, h₃, e, RingHom.algebraMap_toAlgebra]
    ext
    rw [← cancel_mono ((CommRingCat.isPushout_of_isPushout R S R[M]
      (S[M])).op.map Scheme.Spec).isoPullback.hom]
    ext
    · simpa [Functor.Monoidal.μ_of_cartesianMonoidalCategory, RingHom.algebraMap_toAlgebra,
        AlgHom.toUnder, h₁] using
        congr($goal ≫ Spec.map (CommRingCat.ofHom (Bialgebra.comulAlgHom R R[M]).toRingHom))
    · simp [Functor.Monoidal.μ_of_cartesianMonoidalCategory, RingHom.algebraMap_toAlgebra,
        AlgHom.toUnder, h₄, h₅, TensorProduct.algebraMap_def, pullback.condition]))
  fun {X Y} f ↦ by
  ext : 2
  simp only [Functor.CoreMonoidal.toMonoidal_toLaxMonoidal, Functor.comp_obj, Functor.op_obj,
    commMonAlg_obj, Functor.leftOp_obj, commBialgCatEquivComonCommAlgCat_functor_obj,
    Functor.mapMon_obj_X, Equivalence.op_functor, commAlgCatEquivUnder_functor_obj,
    Over.opEquivOpUnder_inverse_obj, Functor.id_obj, Functor.const_obj_obj, CommRingCat.mkUnder_hom,
    Over.post_obj, Spec_obj, Over.mk_left, Over.mk_hom, Spec_map, Quiver.Hom.unop_op,
    Over.pullback_obj_left, Functor.comp_map, Functor.op_map, commMonAlg_map, Functor.leftOp_map,
    commBialgCatEquivComonCommAlgCat_functor_map, CommBialgCat.hom_ofHom, AlgHom.toRingHom_eq_coe,
    Mon_.comp_hom', Functor.mapMon_map_hom, commAlgCatEquivUnder_functor_map, CommAlgCat.hom_ofHom,
    Over.opEquivOpUnder_inverse_map, Over.post_map, Over.homMk_left, Mon_.mkIso_hom_hom,
    Over.comp_left, Over.pullback_map_left, Over.isoMk_hom_left, Iso.symm_hom]
  rw [Iso.eq_inv_comp, ← Category.assoc, Iso.comp_inv_eq]
  ext
  · simp only [RingHom.algebraMap_toAlgebra, CommRingCat.ofHom_hom, Category.assoc, limit.lift_π,
      Over.mk_left, Over.mk_hom, Functor.id_obj, Quiver.Hom.unop_op, Functor.const_obj_obj, id_eq,
      Over.homMk_left, Spec_map, Spec_obj, PullbackCone.mk_pt, PullbackCone.mk_π_app,
      IsPullback.isoPullback_hom_fst_assoc, ← Spec.map_comp, IsPullback.isoPullback_hom_fst]
    congr 1
    ext : 2
    simp
    sorry
  · sorry

-- def Mon.representableBy (S : Scheme.{u}) (M : Type u) [CommMonoid M] :
--     ((Over.forget S).op ⋙ Scheme.Γ ⋙ forget₂ _ CommMonCat ⋙
--       CommMonCat.coyoneda.obj (op (.of M)) ⋙ forget _).RepresentableBy
--       (OverClass.asOver (Mon S M) S) :=
--   letI e : opOp CommMonCat ⋙ yoneda.obj (op (.of M)) ≅ CommMonCat.coyoneda.obj _ ⋙ forget _ :=
--     Coyoneda.opIso.app (op _) ≪≫ CommMonCat.coyonedaForget.symm.app (op (.of M))
--   letI e' := isoWhiskerLeft ((Over.forget S).op ⋙ Scheme.Γ ⋙ forget₂ _ CommMonCat) e
--   ((((((Over.mapPullbackAdj (specULiftZIsTerminal.from S)).comp
--     (Over.equivalenceOfIsTerminal specULiftZIsTerminal).toAdjunction)).comp
--     ΓSpec.adjunction).comp (CommRingCat.forget₂Adj CommRingCat.isInitial).op).representableBy
--     (op (.of M))).ofIso e'


end

end AlgebraicGeometry.Scheme
