/-
Copyright (c) 2025 Yaël Dillies, Christian Merten, Michał Mrugała, Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Christian Merten, Michał Mrugała, Andrew Yang
-/
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.HopfAlgebra.Basic
import Toric.Mathlib.Algebra.Category.Ring.Under.Basic
import Toric.Mathlib.AlgebraicGeometry.AffineScheme
import Toric.Mathlib.CategoryTheory.Limits.Preserves.Finite
import Toric.Mathlib.CategoryTheory.Monoidal.Grp_

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

open AlgebraicGeometry CategoryTheory Opposite Limits

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

section Michal

universe u

variable {R : CommRingCat.{u}} {A B C : Type u}
namespace HopfAlgebra

section
variable [Semiring A] [HopfAlgebra R A]

lemma antipode_anti_comm (a b : A) :
    antipode (R := R) (a * b) = antipode (R := R) b * antipode (R := R) a := by
section
variable [Semiring A] [HopfAlgebra R A]

lemma antipode_anti_comm (a b : A) :
    antipode (R := R) (a * b) = antipode (R := R) b * antipode (R := R) a := by
  sorry
end

section
variable [CommRing A] [HopfAlgebra R A]

lemma antipode_comm (a b : A) :
    antipode (R := R) (a * b) = antipode (R := R) a * antipode (R := R) b := by
  rw [antipode_anti_comm a b, mul_comm]

variable (R A) in
def antipodeAlgHom : A →ₐ[R] A := .ofLinearMap antipode antipode_one antipode_comm

end

end HopfAlgebra

section Algebra

variable [CommRing A] [Algebra R A] [CommRing B] [Algebra R B] [CommRing C] [Algebra R C]

open CommRingCat MonoidalCategory Opposite TensorProduct

lemma UnderOp.rightWhisker_hom (f : A →ₐ[R] B)  :
    (f.toUnder.op ▷ op (R.mkUnder C)).unop.right.hom =
      (Algebra.TensorProduct.map (toAlgHom f.toUnder) (.id _ _)).toRingHom := by
  let F : op (R.mkUnder B) ⊗ op (R.mkUnder C) ⟶ op (R.mkUnder A) ⊗ op (R.mkUnder C) :=
    (Algebra.TensorProduct.map (by exact ⟨f.toRingHom, f.commutes'⟩) (.id _ _)).toUnder.op
  show _ = F.unop.right.hom
  congr 3
  ext
  · simp
    rfl
  simp only [ChosenFiniteProducts.whiskerRight_snd]
  apply Quiver.Hom.unop_inj
  ext (x : R.mkUnder C)
  trans ((1 : R.mkUnder B) ⊗ₜ[R] x:)
  · rfl
  trans (f 1) ⊗ₜ[R] x
  · simp
  · rfl

lemma UnderOp.leftWhisker_hom (f : A →ₐ[R] B) :
    (op (R.mkUnder C) ◁ f.toUnder.op).unop.right.hom =
      (Algebra.TensorProduct.map (.id R (R.mkUnder C)) (toAlgHom f.toUnder)).toRingHom := by
  let F : op (R.mkUnder C) ⊗ op (R.mkUnder B) ⟶ op (R.mkUnder C) ⊗ op (R.mkUnder A) :=
    (Algebra.TensorProduct.map (.id _ _) (by exact ⟨f.toRingHom, f.commutes'⟩)).toUnder.op
  show _ = F.unop.right.hom
  congr 3
  ext
  · simp only [ChosenFiniteProducts.whiskerLeft_fst]
    apply Quiver.Hom.unop_inj
    ext (x : R.mkUnder C)
    trans (x ⊗ₜ[R] (1 : R.mkUnder B):)
    · rfl
    trans x ⊗ₜ[R] f 1
    · simp
    · rfl
  · simp
    rfl

end Algebra

variable [CommRing A] [inst : HopfAlgebra R A]

open CommRingCat MonoidalCategory

variable (A) in
noncomputable def UnderOp.Unitor.ringHom := (Algebra.TensorProduct.lid R A).symm.toAlgHom

-- (UnderOp.Unitor.ringHom A).toRingHom
example : toAlgHom (unop (λ_ (op (R.mkUnder A))).hom) =
    (Algebra.TensorProduct.map (.mk (R := R) (.id R) (fun _ ↦ rfl)) (.mk (R := R) (.id A) (fun _ ↦ rfl)))
      ∘ (Algebra.TensorProduct.lid R A).symm.toAlgHom
    := by
  sorry

noncomputable def UnderOp.Unitor.hom : 𝟙_ (Under R)ᵒᵖ ⊗ op (R.mkUnder A) ⟶ op (R.mkUnder A) := by
  apply op
  change R.mkUnder A ⟶ _
  refine (Algebra.TensorProduct.lid R A).symm.toAlgHom.toUnder ≫
      (Algebra.TensorProduct.map ?_ ?_).toUnder
  · exact .mk (.id R) (fun _ ↦ rfl)
  exact .mk (.id A) (fun _ ↦ rfl)

lemma UnderOp.Unitor.hom_eq : (λ_ (op (R.mkUnder A))).hom = UnderOp.Unitor.hom := rfl

-- def UnderOp.rightWhiskerHom {}

-- noncomputable def UnderOp.RightWhisker.hom :
--   op (R.mkUnder R) ⊗ op (R.mkUnder A) ⟶
--   op (R.mkUnder A) ⊗ op (R.mkUnder A) := by
--   apply op
--   change unop (op (R.mkUnder A) ⊗ _) ⟶ unop ((op (Under.mk (𝟙 R))) ⊗ _)
--   refine (Algebra.TensorProduct.map ?_ ?_).toUnder
--   · exact @AlgHom.mk _ _ _ _ _ _ _ (_) ((Bialgebra.counitAlgHom R A).toRingHom) (Bialgebra.counitAlgHom (↑R) A).commutes'
--   exact @AlgHom.mk _ _ _ _ _ _ _ (_) (.id _) fun _ ↦ rfl

open TensorProduct

def mkUnderRightEquiv (R : CommRingCat) (A : Type*) [CommRing A] [Algebra R A] :
    (R.mkUnder A).right ≃ₐ[R] A where
  __ := RingEquiv.refl _
  commutes' _ := rfl

variable (R A) in
noncomputable
def tensorProductMkUnder : A ⊗[R] A →ₐ[R] (R.mkUnder A).right ⊗[R] (R.mkUnder A).right :=
  Algebra.TensorProduct.map (mkUnderRightEquiv R A).symm (mkUnderRightEquiv R A).symm

-- noncomputable
-- def HopfAlgebra.Grp_one := (Bialgebra.counitAlgHom R A)

lemma foo : (Bialgebra.counitAlgHom R A).toUnder.op ▷ op (R.mkUnder A) ≫
      ((tensorProductMkUnder R A).comp (Bialgebra.comulAlgHom R A)).toUnder.op =
        (λ_ (op (R.mkUnder A))).hom := by
  apply Quiver.Hom.unop_inj
  ext x
  simp only [AlgHom.toUnder_comp, op_comp, unop_comp, Quiver.Hom.unop_op, Category.assoc,
    Under.comp_right, CommRingCat.hom_comp, UnderOp.rightWhisker_hom, AlgHom.toRingHom_eq_coe,
    RingHom.coe_comp, Function.comp_apply, AlgHom.toUnder_right, Bialgebra.comulAlgHom_apply]
  convert DFunLike.congr_arg
      (Algebra.TensorProduct.map (AlgHom.id R R) (mkUnderRightEquiv R A).symm.toAlgHom)
      (Coalgebra.rTensor_counit_comul (R := R) x)
  induction CoalgebraStruct.comul (R := R) x with
  | zero => simp
  | tmul x y => rfl
  | add x y _ _ => simp_all

-- whatsnew in
set_option trace.profiler true in
-- set_option maxHeartbeats 0 in
noncomputable instance : Mon_Class <| op <| CommRingCat.mkUnder R A where
  one := (Bialgebra.counitAlgHom R A).toUnder.op
  mul := ((tensorProductMkUnder R A).comp (Bialgebra.comulAlgHom R A)).toUnder.op
  one_mul' := by
    apply Quiver.Hom.unop_inj
    ext x
    simp only [AlgHom.toUnder_comp, op_comp, unop_comp, Quiver.Hom.unop_op, Category.assoc,
      Under.comp_right, CommRingCat.hom_comp, UnderOp.rightWhisker_hom, AlgHom.toRingHom_eq_coe,
      RingHom.coe_comp, Function.comp_apply, AlgHom.toUnder_right, Bialgebra.comulAlgHom_apply]
    convert DFunLike.congr_arg
        (Algebra.TensorProduct.map (AlgHom.id R R) (mkUnderRightEquiv R A).symm.toAlgHom)
        (Coalgebra.rTensor_counit_comul (R := R) x)
    induction CoalgebraStruct.comul (R := R) x with
    | zero => simp
    | tmul x y => rfl
    | add x y _ _ => simp_all
  mul_one' := by
    apply Quiver.Hom.unop_inj
    ext x
    simp only [AlgHom.toUnder_comp, op_comp, unop_comp, Quiver.Hom.unop_op, Category.assoc,
      Under.comp_right, CommRingCat.hom_comp, UnderOp.leftWhisker_hom, AlgHom.toRingHom_eq_coe,
      RingHom.coe_comp, Function.comp_apply, AlgHom.toUnder_right, Bialgebra.comulAlgHom_apply]
    convert DFunLike.congr_arg (Algebra.TensorProduct.map
          (mkUnderRightEquiv R A).symm.toAlgHom (AlgHom.id R R))
        (Coalgebra.lTensor_counit_comul (R := R) x)
    induction CoalgebraStruct.comul (R := R) x with
    | zero => simp
    | tmul x y => rfl
    | add x y _ _ => simp_all
  mul_assoc' := sorry
  -- inv := op <| (HopfAlgebra.antipodeAlgHom R A).toUnder
  -- left_inv' := sorry
  -- right_inv' := sorry

-- #print prefix instGrp_ClassOppositeUnderCommRingCatOpMkUnder_toric

#exit

end Michal

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
