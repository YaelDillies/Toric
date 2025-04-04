/-
Copyright (c) 2025 Yaël Dillies, Christian Merten, Michał Mrugała, Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Christian Merten, Michał Mrugała, Andrew Yang
-/
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.RingTheory.Bialgebra.Hom
import Toric.Hopf.CommAlg
import Toric.Mathlib.CategoryTheory.Comma.Over.Basic
import Toric.Mathlib.CategoryTheory.Limits.Preserves.Basic
import Toric.Mathlib.CategoryTheory.Monoidal.Grp_
import Toric.Mathlib.RingTheory.Bialgebra.Basic
import Toric.Mathlib.RingTheory.HopfAlgebra.Basic

/-!
# The equivalence between Hopf algebras and affine group schemes

This file constructs `Spec` as a functor from `R`-Hopf algebras to group schemes over `Spec R`,
shows it is full and faithful, and has affine group schemes as essential image.

We want to show that Hopf algebras correspond to affine group schemes. This can easily be done
categorically assuming both categories on either side are defined thoughtfully. However, the
categorical version will not be workable with if we do not also have links to the non-categorical
notions. Therefore, one solution would be to build the left, top and right edges of the following
diagram so that the bottom edge can be obtained by composing the three.

```
  Cogrp Mod_R ≌ Grp AffSch_{Spec R} ≌ Aff Grp Sch_{Spec R}
      ↑ ↓                                      ↑ ↓
R-Hopf algebras         ≃       Affine group schemes over Spec R
```

If we do not care about going back from affine group schemes over `Spec R` to `R`-Hopf algebras
(eg because all our affine group schemes are given as the `Spec` of some algebra), then we can
follow the following simpler diagram:

```
  Cogrp Mod_R   ⥤        Grp Sch_{Spec R}
      ↑ ↓                        ↓
R-Hopf algebras → Affine group schemes over Spec R
```
where the top `≌` comes from the essentially surjective functor `Cogrp Mod_R ⥤ Grp Sch_{Spec R}`,
so that in particular we do not easily know that its inverse is given by `Γ`.
-/

open AlgebraicGeometry Scheme CategoryTheory Opposite Limits Mon_Class Grp_Class

attribute [local instance] Over.chosenFiniteProducts -- From #21399

universe u
variable {R : CommRingCat.{u}}

/-!
### Left edge: `R`-Hopf algebras correspond to cogroup objects under `R`

In this section, we provide ways to turn an unbundled `R`-Hopf algebra into a bundled cogroup
object under `R`, and vice versa.
-/

section leftEdge

section hopfToGrp
variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B] [HopfAlgebra R A] [HopfAlgebra R B]
  {f : A →ₐc[R] B}

noncomputable instance : Grp_Class <| op <| CommAlg.of R A where
  one := (CommAlg.ofHom <| Bialgebra.counitAlgHom R A).op
  mul := (CommAlg.ofHom <| Bialgebra.comulAlgHom R A).op
  one_mul' := by
    apply Quiver.Hom.unop_inj
    ext x
    convert Coalgebra.rTensor_counit_comul (R := R) x
    simp [-Coalgebra.rTensor_counit_comul, CommAlg.rightWhisker_hom]
    rfl
  mul_one' := by
    apply Quiver.Hom.unop_inj
    ext x
    convert Coalgebra.lTensor_counit_comul (R := R) x
    simp [-Coalgebra.lTensor_counit_comul, CommAlg.leftWhisker_hom]
    rfl
  mul_assoc' := by
    apply Quiver.Hom.unop_inj
    ext x
    convert (Coalgebra.coassoc_symm_apply (R := R) x).symm
      <;> simp [-Coalgebra.coassoc_symm_apply, CommAlg.associator_hom_unop_hom,
      CommAlg.rightWhisker_hom, CommAlg.leftWhisker_hom] <;> rfl
  inv := (CommAlg.ofHom <| HopfAlgebra.antipodeAlgHom R A).op
  left_inv' := by
    apply Quiver.Hom.unop_inj
    ext (x : A)
    refine .trans ?_ (HopfAlgebra.mul_antipode_rTensor_comul_apply (R := R) x)
    change (ChosenFiniteProducts.lift (CommAlg.ofHom (HopfAlgebra.antipodeAlgHom R A)).op
      (𝟙 _)).unop.hom (CoalgebraStruct.comul (R := R) x) = _
    induction CoalgebraStruct.comul (R := R) x with
    | zero => simp
    | tmul x y => rfl
    | add x y _ _ => simp_all
  right_inv' := by
    apply Quiver.Hom.unop_inj
    ext (x : A)
    refine .trans ?_ (HopfAlgebra.mul_antipode_lTensor_comul_apply (R := R) x)
    change (ChosenFiniteProducts.lift (𝟙 _) (CommAlg.ofHom
      (HopfAlgebra.antipodeAlgHom R A)).op).unop.hom (CoalgebraStruct.comul (R := R) x) = _
    induction CoalgebraStruct.comul (R := R) x with
    | zero => simp
    | tmul x y => rfl
    | add x y _ _ => simp_all

instance : IsMon_Hom (CommAlg.ofHom (f : A →ₐ[R] B)).op where
   one_hom := by
     apply Quiver.Hom.unop_inj
     ext
     simp [one]
   mul_hom := by
     apply Quiver.Hom.unop_inj
     ext
     simp only [mul, unop_comp, Quiver.Hom.unop_op, CommAlg.hom_comp, CommAlg.hom_ofHom,
         CommAlg.tensorHom_unop_hom]
     rw [BialgHomClass.map_comp_comulAlgHom]

end hopfToGrp

section grpToHopf
variable {R : Type u} [CommRing R] {G : (CommAlg.{u} R)ᵒᵖ} [Grp_Class G]

open MonoidalCategory

noncomputable instance : Bialgebra R G.unop :=
  .mkAlgHoms μ[G].unop.hom η[G].unop.hom
  (by
    convert congr(($((Mon_Class.mul_assoc_flip G).symm)).unop.hom)
    · simp [-Mon_Class.mul_assoc]
      rw [CommAlg.associator_inv_unop_hom]
      rw [← Quiver.Hom.op_unop μ[G]]
      rw [CommAlg.rightWhisker_hom]
      simp
      rfl
    simp
    rw [← Quiver.Hom.op_unop μ[G]]
    rw [CommAlg.leftWhisker_hom]
    rfl)
  (by
    convert congr(($(Mon_Class.one_mul G)).unop.hom)
    simp [-Mon_Class.one_mul]
    rw [← Quiver.Hom.op_unop η[G]]
    rw [CommAlg.rightWhisker_hom]
    rfl)
  (by
    convert congr(($(Mon_Class.mul_one G)).unop.hom)
    simp [-Mon_Class.mul_one]
    rw [← Quiver.Hom.op_unop η[G]]
    rw [CommAlg.leftWhisker_hom]
    rfl)

noncomputable instance : HopfAlgebra R G.unop where
  antipode := ι[G].unop.hom.toLinearMap
  mul_antipode_rTensor_comul := by
    convert congr(($(Grp_Class.left_inv G)).unop.hom.toLinearMap)
    simp [-Grp_Class.left_inv]
    rw [← LinearMap.comp_assoc]
    congr 1
    ext
    rfl
  mul_antipode_lTensor_comul := by
    convert congr(($(Grp_Class.right_inv G)).unop.hom.toLinearMap)
    simp [-Grp_Class.right_inv]
    rw [← LinearMap.comp_assoc]
    congr 1
    ext
    rfl

variable {H : (CommAlg R)ᵒᵖ} [Grp_Class H] (f : G ⟶ H) [IsMon_Hom f]

/-- The coalgebra hom coming from a group morphism in the category of algebras. -/
def IsMon_Hom.toCoalgHom : H.unop →ₗc[R] G.unop where
  __ := f.unop.hom
  map_smul' := by simp
  counit_comp := congr(($(IsMon_Hom.one_hom (f := f))).unop.hom.toLinearMap)
  map_comp_comul := by
    convert congr(($((IsMon_Hom.mul_hom (f := f)).symm)).unop.hom.toLinearMap)
    simp
    rw [←Quiver.Hom.op_unop (f ⊗ f)]
    show _ = (CommAlg.Hom.hom ((unop f).op ⊗ (unop f).op).unop).toLinearMap
        ∘ₗ (CommAlg.Hom.hom μ[H].unop).toLinearMap
    rw [CommAlg.tensorHom_unop_hom]
    congr 1

/-- The Hopf algebra hom coming from a group morphism in the category of algebras. -/
def IsMon_Hom.toBialgHom : H.unop →ₐc[R] G.unop where
  __ := IsMon_Hom.toCoalgHom f
  __ := f.unop.hom

end grpToHopf

end leftEdge

/-!
### Top edge: `Spec` as a functor on Hopf algebras

In this section we construct `Spec` as a functor from `R`-Hopf algebras to affine group schemes over
`Spec R`.
-/

section topEdge

variable (R) in
/-- `Spec` as a functor from `R`-algebras to schemes over `Spec R`. -/
noncomputable abbrev algSpec : (CommAlg R)ᵒᵖ ⥤ Over (Spec R) :=
  (commAlgEquivUnder R).op.functor ⋙ (Over.opEquivOpUnder R).inverse ⋙ Over.post Scheme.Spec

-- FIXME: Neither `inferInstance` nor `by unfold algSpec; infer_instance` work in the following 3.
-- TODO: Do a MWE once `CommAlg` is in mathlib
instance algSpec.instPreservesLimits : PreservesLimits (algSpec R) :=
  inferInstanceAs <| PreservesLimits <|
    (commAlgEquivUnder R).op.functor ⋙ (Over.opEquivOpUnder R).inverse ⋙ Over.post Scheme.Spec

/-- `Spec` is full on `R`-algebras. -/
instance algSpec.instFull : (algSpec R).Full :=
  inferInstanceAs <| Functor.Full <|
    (commAlgEquivUnder R).op.functor ⋙ (Over.opEquivOpUnder R).inverse ⋙ Over.post Scheme.Spec

/-- `Spec` is faithful on `R`-algebras. -/
instance algSpec.instFaithful : (algSpec R).Faithful :=
  inferInstanceAs <| Functor.Faithful <|
    (commAlgEquivUnder R).op.functor ⋙ (Over.opEquivOpUnder R).inverse ⋙ Over.post Scheme.Spec

/-- `Spec` is fully faithful on `R`-algebras, with inverse `Gamma`. -/
noncomputable def algSpec.fullyFaithful : (algSpec R).FullyFaithful :=
  ((commAlgEquivUnder R).op.trans (Over.opEquivOpUnder R).symm).fullyFaithfulFunctor.comp
    Spec.fullyFaithful.over

variable (R) in
/-- `Spec` as a functor from `R`-Hopf algebras to group schemes over `Spec R`. -/
noncomputable abbrev hopfSpec : Grp_ (CommAlg R)ᵒᵖ ⥤ Grp_ (Over <| Spec R) := (algSpec R).mapGrp

/-- `Spec` is full on `R`-Hopf algebras. -/
instance hopfSpec.instFull : (hopfSpec R).Full := inferInstance

/-- `Spec` is faithful on `R`-Hopf algebras. -/
instance hopfSpec.instFaithful : (hopfSpec R).Faithful := inferInstance

/-- `Spec` is fully faithful on `R`-Hopf algebras, with inverse `Gamma`. -/
noncomputable def hopfSpec.fullyFaithful : (hopfSpec R).FullyFaithful :=
  algSpec.fullyFaithful.mapGrp

end topEdge

/-!
### Right edge: The essential image of `Spec` on Hopf algebras

In this section we show that the essential image of `R`-Hopf algebras under `Spec` is precisely
affine group schemes over `Spec R`.
-/

section rightEdge

/-- The essential image of `R`-algebras under `Spec` is precisely affine schemes over `Spec R`. -/
@[simp]
lemma essImage_algSpec {G : Over <| Spec R} : (algSpec R).essImage G ↔ IsAffine G.left := sorry

/-- The essential image of `R`-Hopf algebras under `Spec` is precisely affine group schemes over
`Spec R`. -/
@[simp]
lemma essImage_hopfSpec {G : Grp_ (Over <| Spec R)} :
    (hopfSpec R).essImage G ↔ IsAffine G.X.left := by simp [hopfSpec]

end rightEdge
