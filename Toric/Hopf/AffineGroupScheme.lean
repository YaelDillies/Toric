/-
Copyright (c) 2025 Yaël Dillies, Christian Merten, Michał Mrugała, Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Christian Merten, Michał Mrugała, Andrew Yang
-/
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.RingTheory.HopfAlgebra.Basic
import Toric.Mathlib.Algebra.Category.Ring.Under.Basic
import Toric.Hopf.CommAlg
import Toric.Mathlib.AlgebraicGeometry.AffineScheme
import Toric.Mathlib.CategoryTheory.Limits.Preserves.Finite
import Toric.Mathlib.CategoryTheory.Monoidal.Grp_
import Toric.Mathlib.RingTheory.HopfAlgebra.Basic
import Toric.Mathlib.RingTheory.Bialgebra.Basic
import Toric.Mathlib.CategoryTheory.Monoidal.Mon_

/-!
# The equivalence between Hopf algebras and affine group schemes

This file constructs `Spec` as a functor from `R`-Hopf algebras to group schemes over `Spec R`,
shows it is full and faithful, and has affine group schemes as essential image.

We want to show that Hopf algebras correspond to affine group schemes. This can easily be done
categorically assuming both categories on either side are defined thoughtfully. However, the
categorical version will not be workable with if we do not also have links to the non-categorical
notions. Therefore, we will build the left, top and right edges of the following diagram so that
the bottom edge can be obtained by composing the three.

```
   Cogrp Mod_R →     Grp Sch_{Spec R}
        ↓                    ↓
R-Hopf algebra → Group scheme over Spec R
```
-/

open AlgebraicGeometry CategoryTheory Opposite Limits Mon_Class

attribute [local instance] Over.chosenFiniteProducts -- From #21399

variable {R : CommRingCat}

/-!
### Top edge: equivalence of categories

In this section we show that the category of cogroup objects of rings under a ring `R` is equivalent
 to the category of group objects of schemes over `Spec R`.
-/

noncomputable def algEquivSch : (Under R)ᵒᵖ ≌ Over <| AffineScheme.Spec.obj <| .op R :=
  (Over.opEquivOpUnder R).symm.trans <|
    Over.postEquiv (.op R) AffineScheme.equivCommRingCat.symm

noncomputable def hopfAlgEquivAffGrpSch :
    Grp_ (Under R)ᵒᵖ ≌ Grp_ (Over <| AffineScheme.Spec.obj <| .op R) :=
  .mapGrp algEquivSch

variable (R) in
/-- `Spec` as a functor from `R`-Hopf algebras to group schemes over `Spec R`. -/
noncomputable abbrev hopfSpec : Grp_ (Under R)ᵒᵖ ⥤ Grp_ (Over <| Spec R) :=
  (((Over.opEquivOpUnder R).inverse ⋙ Over.post Scheme.Spec).mapGrp:)

/-- `Spec` is full on `R`-Hopf algebras. -/
instance hopfSpec.instFull : (hopfSpec R).Full := inferInstance

/-- `Spec` is faithful on `R`-Hopf algebras. -/
instance hopfSpec.instFaithful : (hopfSpec R).Faithful := inferInstance

/-!
### Left edge: `R`-Hopf algebras correspond to cogroup objects under `R`

In this section, we provide ways to turn an unbundled `R`-Hopf algebra into a bundled cogroup
object under `R`, and vice versa.
-/

section leftEdge

universe u

variable {R : CommRingCat.{u}}

section hopfToGrp

variable  {A : Type u} [CommRing A] [HopfAlgebra R A]

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

end hopfToGrp

section grpToHopfObj

variable {G : (CommAlg.{u} R)ᵒᵖ} [Grp_Class G]

open MonoidalCategory

variable {C : Type*} [Category C] [MonoidalCategory C]

noncomputable
instance : Bialgebra R G.unop :=
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


end grpToHopfObj

end leftEdge

/-!
### Right edge: Group schemes corresponds to group objects in the category of schemes

Mathlib already provides tooling for turning a bundled group objects into an unbundled group object
and back, so there is nothing to be done here.

### Bottom edge: transferring between unbundled objects

In this section we provide ways to turn an unbundled `R`-Hopf algebra into an unbundled group
scheme over `R`, and vice-verse.
-/

noncomputable instance Gamma.instAlgebra (G : Scheme) [OverClass G (Spec R)] : Algebra R Γ(G, ⊤) :=
  RingHom.toAlgebra <| CommRingCat.Hom.hom <| (Scheme.ΓSpecIso R).inv ≫ Scheme.Γ.map (G ↘ Spec R).op

/-- For an `R`-algebraic group `G`, this is the global sections `Γ(G)` as a `R`-algebra. -/
noncomputable abbrev algebraGamma (G : Over <| Spec R) [Grp_Class G] : Under R :=
  .mk <| CommRingCat.ofHom <| algebraMap R Γ(G.left, ⊤)

instance (G : Over <| Spec R) [Grp_Class G] : Grp_Class (op <| algebraGamma G) := sorry

-- Yaël: I think this technically belongs to the top edge?
/-- The essential image of `R`-Hopf algebras under `Spec` is precisely affine group schemes over
`Spec R`. -/
@[simp]
lemma essImage_hopfSpec {G : Grp_ (Over <| Spec R)} :
    (hopfSpec R).essImage G ↔ IsAffine G.X.left where
  mp hG := by
    let e : G.X.left ⟶ Spec hG.witness.X.unop.right := ((Grp_.forget _).map hG.getIso.inv).left
    exact .of_isIso e
  mpr _ := by
    refine ⟨.mk' <| .op <| algebraGamma G.X,
      ⟨Grp_.mkIso (Over.isoMk G.X.left.isoSpec.symm ?_) ?_ ?_⟩⟩
    · simp
      sorry
    · ext : 1
      simp
      sorry
    · sorry
