/-
Copyright (c) 2025 Yaël Dillies, Michał Mrugała. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Michał Mrugała
-/
import Mathlib.Algebra.Category.CommBialgCat
import Mathlib.CategoryTheory.Monoidal.Grp_
import Mathlib.RingTheory.HopfAlgebra.TensorProduct
import Toric.Mathlib.RingTheory.HopfAlgebra.Convolution

/-!
# The category of commutative Hopf algebras over a commutative ring

This file defines the bundled category `CommHopfAlgCat` of commutative Hopf algebras over a fixed
commutative ring `R` along with the forgetful functor to `CommBialgCat`.
-/

noncomputable section

open CategoryTheory Coalgebra HopfAlgebra Limits

universe v u
variable {R : Type u} [CommRing R]

variable (R) in
/-- The category of commutative `R`-Hopf algebras and their morphisms. -/
structure CommHopfAlgCat where
  private mk ::
  /-- The underlying type. -/
  carrier : Type v
  [commRing : CommRing carrier]
  [hopfAlgebra : HopfAlgebra R carrier]

namespace CommHopfAlgCat
variable {A B C : CommHopfAlgCat.{v} R} {X Y Z : Type v} [CommRing X] [HopfAlgebra R X]
  [CommRing Y] [HopfAlgebra R Y] [CommRing Z] [HopfAlgebra R Z]

attribute [instance] commRing hopfAlgebra

initialize_simps_projections CommHopfAlgCat (-commRing, -hopfAlgebra)

instance : CoeSort (CommHopfAlgCat R) (Type v) := ⟨carrier⟩

attribute [coe] CommHopfAlgCat.carrier

variable (R) in
/-- Turn an unbundled `R`-Hopf algebra into the corresponding object in the category of
`R`-Hopf algebras.

This is the preferred way to construct a term of `CommHopfAlgCat R`. -/
abbrev of (X : Type v) [CommRing X] [HopfAlgebra R X] : CommHopfAlgCat.{v} R := ⟨X⟩

variable (R) in
lemma coe_of (X : Type v) [CommRing X] [HopfAlgebra R X] : (of R X : Type v) = X := rfl

/-- The type of morphisms in `CommHopfAlgCat R`. -/
@[ext]
structure Hom (A B : CommHopfAlgCat.{v} R) where
  private mk ::
  /-- The underlying bialgebra map. -/
  hom' : A →ₐc[R] B

instance : Category (CommHopfAlgCat.{v} R) where
  Hom A B := Hom A B
  id A := ⟨.id R A⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

instance : ConcreteCategory (CommHopfAlgCat.{v} R) (· →ₐc[R] ·) where
  hom := Hom.hom'
  ofHom := Hom.mk

/-- Turn a morphism in `CommHopfAlgCat` back into a `BialgHom`. -/
abbrev Hom.hom (f : Hom A B) := ConcreteCategory.hom (C := CommHopfAlgCat R) f

/-- Typecheck a `BialgHom` as a morphism in `CommHopfAlgCat R`. -/
abbrev ofHom {_ : CommRing X} {_ : CommRing Y} {_ : HopfAlgebra R X} {_ : HopfAlgebra R Y}
    (f : X →ₐc[R] Y) : of R X ⟶ of R Y := ConcreteCategory.ofHom (C := CommHopfAlgCat R) f

/-- Use the `ConcreteCategory.hom` projection for `@[simps]` lemmas. -/
def Hom.Simps.hom (A B : CommHopfAlgCat.{v} R) (f : Hom A B) := f.hom

initialize_simps_projections Hom (hom' → hom)

/-!
The results below duplicate the `ConcreteCategory` simp lemmas, but we can keep them for `dsimp`.
-/

@[simp] lemma hom_id : (𝟙 A : A ⟶ A).hom = AlgHom.id R A := rfl

/- Provided for rewriting. -/
lemma id_apply (A : CommHopfAlgCat.{v} R) (a : A) : (𝟙 A : A ⟶ A) a = a := by simp

@[simp] lemma hom_comp (f : A ⟶ B) (g : B ⟶ C) : (f ≫ g).hom = g.hom.comp f.hom := rfl

/- Provided for rewriting. -/
lemma comp_apply (f : A ⟶ B) (g : B ⟶ C) (a : A) : (f ≫ g) a = g (f a) := by simp

@[simp] lemma hom_ofHom (f : X →ₐc[R] Y) : (ofHom f).hom = f := rfl
@[simp] lemma ofHom_hom (f : A ⟶ B) : ofHom f.hom = f := rfl

@[simp] lemma ofHom_id : ofHom (.id R X) = 𝟙 (of R X) := rfl

@[simp]
lemma ofHom_comp (f : X →ₐc[R] Y) (g : Y →ₐc[R] Z) : ofHom (g.comp f) = ofHom f ≫ ofHom g := rfl

lemma ofHom_apply (f : X →ₐc[R] Y) (x : X) : ofHom f x = f x := rfl

lemma inv_hom_apply (e : A ≅ B) (x : A) : e.inv (e.hom x) = x := by simp
lemma hom_inv_apply (e : A ≅ B) (x : B) : e.hom (e.inv x) = x := by simp

instance : Inhabited (CommHopfAlgCat R) := ⟨of R R⟩

lemma forget_obj (A : CommHopfAlgCat.{v} R) : (forget (CommHopfAlgCat.{v} R)).obj A = A := rfl

lemma forget_map (f : A ⟶ B) : (forget (CommHopfAlgCat.{v} R)).map f = f := rfl

instance : CommRing ((forget (CommHopfAlgCat R)).obj A) := inferInstanceAs <| CommRing A

instance : HopfAlgebra R ((forget (CommHopfAlgCat R)).obj A) := inferInstanceAs <| HopfAlgebra R A

instance hasForgetToCommBialgCat : HasForget₂ (CommHopfAlgCat.{v} R) (CommBialgCat.{v} R) where
  forget₂.obj A := .of R A
  forget₂.map f := CommBialgCat.ofHom f.hom

@[simp] lemma forget₂_commBialgCat_obj (A : CommHopfAlgCat.{v} R) :
    (forget₂ (CommHopfAlgCat.{v} R) (CommBialgCat.{v} R)).obj A = .of R A := rfl

@[simp] lemma forget₂_commBialgCat_map (f : A ⟶ B) :
    (forget₂ (CommHopfAlgCat.{v} R) (CommBialgCat.{v} R)).map f = CommBialgCat.ofHom f.hom := rfl

/-- Forgetting to the underlying type and then building the bundled object returns the original Hopf
algebra. -/
@[simps]
def ofSelfIso (A : CommHopfAlgCat.{v} R) : of R A ≅ A where
  hom := 𝟙 A
  inv := 𝟙 A

/-- Build an isomorphism in the category `CommHopfAlgCat R` from a `BialgEquiv` between
`HopfAlgebra`s. -/
@[simps]
def isoMk {X Y : Type v} {_ : CommRing X} {_ : CommRing Y} {_ : HopfAlgebra R X}
    {_ : HopfAlgebra R Y} (e : X ≃ₐc[R] Y) : of R X ≅ of R Y where
  hom := ofHom (e : X →ₐc[R] Y)
  inv := ofHom (e.symm : Y →ₐc[R] X)

/-- Build a `BialgEquiv` from an isomorphism in the category `CommHopfAlgCat R`. -/
@[simps]
def ofIso (i : A ≅ B) : A ≃ₐc[R] B where
  __ := i.hom.hom
  toFun := i.hom
  invFun := i.inv
  left_inv x := by simp
  right_inv x := by simp

/-- Commutative Hopf algebra equivalences between `HopfAlgebra`s are the same as isomorphisms in
`CommHopfAlgCat R`. -/
@[simps]
def isoEquivBialgEquiv : (of R X ≅ of R Y) ≃ (X ≃ₐc[R] Y) where
  toFun := ofIso
  invFun := isoMk
  left_inv _ := rfl
  right_inv _ := rfl

instance reflectsIsomorphisms_forget : (forget (CommHopfAlgCat.{u} R)).ReflectsIsomorphisms where
  reflects {X Y} f _ := by
    let i := asIso ((forget (CommHopfAlgCat.{u} R)).map f)
    let e : X ≃ₐc[R] Y := { f.hom, i.toEquiv with }
    exact (isoMk e).isIso_hom

end CommHopfAlgCat

attribute [local ext] Quiver.Hom.unop_inj

instance CommAlgCat.grpObjOpOf {A : Type u} [CommRing A] [HopfAlgebra R A] :
    GrpObj (Opposite.op <| CommAlgCat.of R A) where
  inv := (CommAlgCat.ofHom <| antipodeAlgHom R A).op
  left_inv := by
    ext x
    simpa [← Algebra.TensorProduct.lmul'_comp_map, -mul_antipode_rTensor_comul_apply] using
      mul_antipode_rTensor_comul_apply (R := R) x
  right_inv := by
    ext x
    simpa [← Algebra.TensorProduct.lmul'_comp_map, -mul_antipode_lTensor_comul_apply] using
      mul_antipode_lTensor_comul_apply (R := R) x

open Opposite MonObj

@[simp]
lemma CommAlgCat.inv_op_of_unop_hom {A : Type u} [CommRing A] [HopfAlgebra R A] :
    ι[op <| CommAlgCat.of R A].unop.hom = antipodeAlgHom R A := rfl

instance (A : (CommAlgCat R)ᵒᵖ) [GrpObj A] : HopfAlgebra R A.unop :=
  .ofAlgHom ι[A].unop.hom
    congr($(GrpObj.left_inv (X := A)).unop.hom)
    congr($(GrpObj.right_inv (X := A)).unop.hom)

variable (R) in
/-- Commutative Hopf algebras over a commutative ring `R` are the same thing as cogroup
`R`-algebras. -/
@[simps! functor_obj_unop_X inverse_obj unitIso_hom_app
  unitIso_inv_app counitIso_hom_app counitIso_inv_app]
def commHopfAlgCatEquivCogrpCommAlgCat : CommHopfAlgCat R ≌ (Grp (CommAlgCat R)ᵒᵖ)ᵒᵖ where
  functor.obj A := .op <| .mk <| .op <| .of R A
  functor.map {A B} f := .op <| .mk' <| .op <| CommAlgCat.ofHom f.hom
  inverse.obj A := .of R A.unop.X.unop
  inverse.map {A B} f := CommHopfAlgCat.ofHom <| .ofAlgHom f.unop.hom.unop.hom
    congr(($(IsMonHom.one_hom (f := f.unop.hom))).unop.hom)
    congr(($((IsMonHom.mul_hom (f := f.unop.hom)).symm)).unop.hom)
  unitIso.hom := 𝟙 _
  unitIso.inv := 𝟙 _
  counitIso.hom := 𝟙 _
  counitIso.inv := 𝟙 _

instance {A : CommHopfAlgCat.{u} R} [IsCocomm R A] :
    IsCommMonObj ((commHopfAlgCatEquivCogrpCommAlgCat R).functor.obj A).unop.X := by
  dsimp; infer_instance
