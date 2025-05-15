/-
Copyright (c) 2025 Yaël Dillies, Christian Merten, Michał Mrugała, Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Christian Merten, Michał Mrugała, Andrew Yang
-/
import Mathlib.CategoryTheory.Monoidal.Grp_
import Mathlib.RingTheory.Bialgebra.Hom
import Toric.Mathlib.Algebra.Category.CommAlg.Monoidal
import Toric.Mathlib.CategoryTheory.Monoidal.Mon_
import Toric.Mathlib.RingTheory.HopfAlgebra.Basic

/-!
# The category of Hopf algebras

This file shows that `(Grp_ (CommAlg R)ᵒᵖ)ᵒᵖ` is the category of `R`-Hopf algebras, in the sense
that one can go back and forth between `{A : Type*} [CommRing A] [HopfAlgebra R A]` and
`A : (Grp_ (CommAlg R)ᵒᵖ)ᵒᵖ`.
-/

suppress_compilation

open CategoryTheory Opposite Mon_Class Grp_Class

attribute [local ext] Quiver.Hom.unop_inj

universe u
variable {R : CommRingCat.{u}}

/-! ### Going from a `R`-Hopf algebra to a cogroup object in the category of `R`-algebras -/

section bialgToMon
variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B] [Bialgebra R A] [Bialgebra R B]
  {f : A →ₐc[R] B}

instance Mon_Class_op_commAlgOf : Mon_Class <| op <| CommAlg.of R A where
  one := (CommAlg.ofHom <| Bialgebra.counitAlgHom R A).op
  mul := (CommAlg.ofHom <| Bialgebra.comulAlgHom R A).op
  one_mul' := by ext; exact Coalgebra.rTensor_counit_comul _
  mul_one' := by ext; exact Coalgebra.lTensor_counit_comul _
  mul_assoc' := by ext; exact (Coalgebra.coassoc_symm_apply (R := R) _).symm

instance isMon_Hom_commAlgOfHom : IsMon_Hom (CommAlg.ofHom (f : A →ₐ[R] B)).op where
   one_hom := by ext; simp [one]
   mul_hom := by
    ext
    simp only [mul, unop_comp, Quiver.Hom.unop_op, CommAlg.hom_comp, CommAlg.hom_ofHom,
      CommAlg.tensorHom_unop_hom]
    rw [BialgHomClass.map_comp_comulAlgHom]

end bialgToMon

section hopfToGrp
variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B] [HopfAlgebra R A] [HopfAlgebra R B]
  {f : A →ₐc[R] B}

instance Grp_Class_op_commAlgOf : Grp_Class <| op <| CommAlg.of R A where
  inv := (CommAlg.ofHom <| HopfAlgebra.antipodeAlgHom R A).op
  left_inv' := by
    ext (x : A)
    refine .trans ?_ (HopfAlgebra.mul_antipode_rTensor_comul_apply (R := R) x)
    change (CartesianMonoidalCategory.lift (CommAlg.ofHom (HopfAlgebra.antipodeAlgHom R A)).op
      (𝟙 _)).unop.hom (CoalgebraStruct.comul (R := R) x) = _
    induction CoalgebraStruct.comul (R := R) x with
    | zero => simp
    | tmul x y => rfl
    | add x y _ _ => simp_all
  right_inv' := by
    ext (x : A)
    refine .trans ?_ (HopfAlgebra.mul_antipode_lTensor_comul_apply (R := R) x)
    change (CartesianMonoidalCategory.lift (𝟙 _) (CommAlg.ofHom
      (HopfAlgebra.antipodeAlgHom R A)).op).unop.hom (CoalgebraStruct.comul (R := R) x) = _
    induction CoalgebraStruct.comul (R := R) x with
    | zero => simp
    | tmul x y => rfl
    | add x y _ _ => simp_all

end hopfToGrp

/-! ### Going from a cogroup object in the category of `R`-algebras to a `R`-Hopf algebra -/

section grpToHopf
variable {R : Type u} [CommRing R] {G : (CommAlg.{u} R)ᵒᵖ} [Grp_Class G]

open MonoidalCategory

instance bialgebra_unop : Bialgebra R G.unop :=
  .ofAlgHom μ[G].unop.hom η[G].unop.hom
    congr(($((Mon_Class.mul_assoc_flip G).symm)).unop.hom)
    congr(($(Mon_Class.one_mul G)).unop.hom)
    congr(($(Mon_Class.mul_one G)).unop.hom)

instance hopfAlgebra_unop : HopfAlgebra R G.unop where
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
  map_comp_comul := congr(($((IsMon_Hom.mul_hom (f := f)).symm)).unop.hom.toLinearMap)

/-- The Hopf algebra hom coming from a group morphism in the category of algebras. -/
def IsMon_Hom.toBialgHom : H.unop →ₐc[R] G.unop where
  __ := IsMon_Hom.toCoalgHom f
  __ := f.unop.hom

end grpToHopf

/-! ### Compatibilities -/

section
variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B] [HopfAlgebra R A] [HopfAlgebra R B]
  {f : A →ₐc[R] B}

@[simp]
lemma IsMon_Hom.toBialgHom_commAlgOfHom : toBialgHom (CommAlg.ofHom (f : A →ₐ[R] B)).op = f := rfl

end

section
variable {R : Type u} [CommRing R] {G H : (CommAlg.{u} R)ᵒᵖ} [Grp_Class G] [Grp_Class H]
    {f : G ⟶ H} [IsMon_Hom f]

@[simp] lemma CommAlg.ofHom_toBialgHom : (ofHom (IsMon_Hom.toBialgHom f : _ →ₐ[R] _)).op = f := rfl

end
