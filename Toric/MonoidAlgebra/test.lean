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
lemma prodComparisonIso_pullback_Spec_hom_left' {R S : CommRingCat.{u}} (f : R ⟶ S)
    {A B : Scheme.{u}} (fA : A ⟶ Spec R) (fB : B ⟶ Spec R) :
    (by exact (prodComparisonIso (Over.pullback (Spec.map f)) (Over.mk fA) (Over.mk fB)).inv.left) ≫
      pullback.fst (pullback.fst fA fB ≫ fA) (Spec.map f) ≫
        pullback.fst _ _ = pullback.fst (pullback.snd fA (Spec.map f))
          (pullback.snd fB (Spec.map f)) ≫ pullback.fst _ _ :=
  prodComparisonIso_pullback_Spec_hom_left ..

set_option maxHeartbeats 0 in
attribute [local instance] Functor.Monoidal.ofChosenFiniteProducts in
def foo {R S : CommRingCat.{u}} (f : R ⟶ S) :
    specCommMonAlg R ⋙ (Over.pullback (Spec.map f)).mapMon ≅ specCommMonAlg S :=
  NatIso.ofComponents (fun M ↦ Mon_.mkIso (Over.isoMk (by
    letI := f.hom.toAlgebra
    exact ((CommRingCat.isPushout_of_isPushout R S (MonoidAlgebra R M.unop)
      (MonoidAlgebra S M.unop)).op.map Scheme.Spec).isoPullback.symm) (by dsimp; simp; rfl)) /- (by
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
        (MonoidAlgebra.lift R M.unop (MonoidAlgebra S M.unop)
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
    letI := f.hom.toAlgebra
    ext
    rw [← cancel_mono ((CommRingCat.isPushout_of_isPushout R S (MonoidAlgebra R M.unop)
      (MonoidAlgebra S M.unop)).op.map Scheme.Spec).isoPullback.hom]
    ext
    · have := congr(Spec.map (CommRingCat.ofHom
        $(comulAlgHom_comp_mapRangeRingHom f.hom (M := M.unop))))
      simp only [AlgHom.toRingHom_eq_coe, CommRingCat.ofHom_comp, Spec.map_comp] at this
      simp [Functor.Monoidal.μ_of_cartesianMonoidalCategory, RingHom.algebraMap_toAlgebra,
        AlgHom.toUnder, this]
      simp only [← Category.assoc]
      congr 1
      rw [← Iso.eq_comp_inv]
      ext
      · simp
        sorry
      · simp
        sorry
    · sorry))
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
