/-
Copyright (c) 2025 Yaël Dillies, Michał Mrugała. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Michał Mrugała
-/
import Toric.Mathlib.Algebra.Category.CommAlgCat.Monoidal
import Toric.Mathlib.CategoryTheory.Monoidal.Mon_
import Toric.Mathlib.RingTheory.Bialgebra.Equiv
import Toric.Mathlib.RingTheory.Bialgebra.TensorProduct

/-!
# The category of commutative bialgebras over a commutative ring

This file defines the bundled category `CommBialgCat` of commutative bialgebras over a fixed
commutative ring `R` along with the forgetful functor to `CommAlgCat`.
-/

open Bialgebra Coalgebra

noncomputable section

namespace CategoryTheory

open Bialgebra Limits
open scoped Mon_Class MonoidalCategory

universe v u
variable {R : Type u} [CommRing R]

variable (R) in
/-- The category of commutative `R`-bialgebras and their morphisms. -/
structure CommBialgCat where
  private mk ::
  /-- The underlying type. -/
  carrier : Type v
  [commRing : CommRing carrier]
  [bialgebra : Bialgebra R carrier]

namespace CommBialgCat
variable {A B C : CommBialgCat.{v} R} {X Y Z : Type v} [CommRing X] [Bialgebra R X]
  [CommRing Y] [Bialgebra R Y] [CommRing Z] [Bialgebra R Z]

attribute [instance] commRing bialgebra

initialize_simps_projections CommBialgCat (-commRing, -bialgebra)

instance : CoeSort (CommBialgCat R) (Type v) := ⟨carrier⟩

attribute [coe] CommBialgCat.carrier

variable (R) in
/-- Turn an unbundled `R`-bialgebra into the corresponding object in the category of `R`-bialgebras.

This is the preferred way to construct a term of `CommBialgCat R`. -/
abbrev of (X : Type v) [CommRing X] [Bialgebra R X] : CommBialgCat.{v} R := ⟨X⟩

variable (R) in
lemma coe_of (X : Type v) [CommRing X] [Bialgebra R X] : (of R X : Type v) = X := rfl

/-- The type of morphisms in `CommBialgCat R`. -/
@[ext]
structure Hom (A B : CommBialgCat.{v} R) where
  private mk ::
  /-- The underlying bialgebra map. -/
  hom' : A →ₐc[R] B

instance : Category (CommBialgCat.{v} R) where
  Hom A B := Hom A B
  id A := ⟨.id R A⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

instance : ConcreteCategory (CommBialgCat.{v} R) (· →ₐc[R] ·) where
  hom := Hom.hom'
  ofHom := Hom.mk

/-- Turn a morphism in `CommBialgCat` back into a `BialgHom`. -/
abbrev Hom.hom (f : Hom A B) := ConcreteCategory.hom (C := CommBialgCat R) f

/-- Typecheck a `BialgHom` as a morphism in `CommBialgCat R`. -/
abbrev ofHom {X Y : Type v} {_ : CommRing X} {_ : CommRing Y} {_ : Bialgebra R X}
    {_ : Bialgebra R Y} (f : X →ₐc[R] Y) : of R X ⟶ of R Y :=
  ConcreteCategory.ofHom (C := CommBialgCat R) f

/-- Use the `ConcreteCategory.hom` projection for `@[simps]` lemmas. -/
def Hom.Simps.hom (A B : CommBialgCat.{v} R) (f : Hom A B) := f.hom

initialize_simps_projections Hom (hom' → hom)

/-!
The results below duplicate the `ConcreteCategory` simp lemmas, but we can keep them for `dsimp`.
-/

@[simp] lemma hom_id : (𝟙 A : A ⟶ A).hom = AlgHom.id R A := rfl

/- Provided for rewriting. -/
lemma id_apply (A : CommBialgCat.{v} R) (a : A) : (𝟙 A : A ⟶ A) a = a := by simp

@[simp] lemma hom_comp (f : A ⟶ B) (g : B ⟶ C) : (f ≫ g).hom = g.hom.comp f.hom := rfl

/- Provided for rewriting. -/
lemma comp_apply (f : A ⟶ B) (g : B ⟶ C) (a : A) : (f ≫ g) a = g (f a) := by simp

@[ext] lemma hom_ext {f g : A ⟶ B} (hf : f.hom = g.hom) : f = g := Hom.ext hf

@[simp] lemma hom_ofHom (f : X →ₐc[R] Y) : (ofHom f).hom = f := rfl
@[simp] lemma ofHom_hom (f : A ⟶ B) : ofHom f.hom = f := rfl

@[simp] lemma ofHom_id : ofHom (.id R X) = 𝟙 (of R X) := rfl

@[simp]
lemma ofHom_comp (f : X →ₐc[R] Y) (g : Y →ₐc[R] Z) : ofHom (g.comp f) = ofHom f ≫ ofHom g := rfl

lemma ofHom_apply (f : X →ₐc[R] Y) (x : X) : ofHom f x = f x := rfl

lemma inv_hom_apply (e : A ≅ B) (x : A) : e.inv (e.hom x) = x := by simp [← comp_apply]
lemma hom_inv_apply (e : A ≅ B) (x : B) : e.hom (e.inv x) = x := by simp [← comp_apply]

instance : Inhabited (CommBialgCat R) := ⟨of R R⟩

lemma forget_obj (A : CommBialgCat.{v} R) : (forget (CommBialgCat.{v} R)).obj A = A := rfl

lemma forget_map (f : A ⟶ B) : (forget (CommBialgCat.{v} R)).map f = f := rfl

instance : CommRing ((forget (CommBialgCat R)).obj A) := inferInstanceAs <| CommRing A

instance : Bialgebra R ((forget (CommBialgCat R)).obj A) := inferInstanceAs <| Bialgebra R A

instance hasForgetToCommAlgCat : HasForget₂ (CommBialgCat.{v} R) (CommAlgCat.{v} R) where
  forget₂.obj M := .of R M
  forget₂.map f := CommAlgCat.ofHom f.hom

@[simp] lemma forget₂_commAlgCat_obj (A : CommBialgCat.{v} R) :
    (forget₂ (CommBialgCat.{v} R) (CommAlgCat.{v} R)).obj A = .of R A := rfl

@[simp] lemma forget₂_commAlgCat_map (f : A ⟶ B) :
    (forget₂ (CommBialgCat.{v} R) (CommAlgCat.{v} R)).map f = CommAlgCat.ofHom f.hom := rfl

/-- Forgetting to the underlying type and then building the bundled object returns the original
bialgebra. -/
@[simps]
def ofSelfIso (M : CommBialgCat.{v} R) : of R M ≅ M where
  hom := 𝟙 M
  inv := 𝟙 M

/-- Build an isomorphism in the category `CommBialgCat R` from a `BialgEquiv` between
`Bialgebra`s. -/
@[simps]
def isoMk {X Y : Type v} {_ : CommRing X} {_ : CommRing Y} {_ : Bialgebra R X}
    {_ : Bialgebra R Y} (e : X ≃ₐc[R] Y) : of R X ≅ of R Y where
  hom := ofHom (e : X →ₐc[R] Y)
  inv := ofHom (e.symm : Y →ₐc[R] X)

/-- Build a `BialgEquiv` from an isomorphism in the category `CommBialgCat R`. -/
@[simps]
def ofIso (i : A ≅ B) : A ≃ₐc[R] B where
  __ := i.hom.hom
  toFun := i.hom
  invFun := i.inv
  left_inv x := by simp
  right_inv x := by simp

/-- Bialgebra equivalences between `Bialgebra`s are the same as isomorphisms in `CommBialgCat`. -/
@[simps]
def isoEquivBialgEquiv : (of R X ≅ of R Y) ≃ (X ≃ₐc[R] Y) where
  toFun := ofIso
  invFun := isoMk
  left_inv _ := rfl
  right_inv _ := rfl

instance reflectsIsomorphisms_forget : (forget (CommBialgCat.{u} R)).ReflectsIsomorphisms where
  reflects {X Y} f _ := by
    let i := asIso ((forget (CommBialgCat.{u} R)).map f)
    let e : X ≃ₐc[R] Y := { f.hom, i.toEquiv with }
    exact (isoMk e).isIso_hom

end CommBialgCat

attribute [local ext] Quiver.Hom.unop_inj

/-- Implementation detail of `commBialgCatEquivComonCommAlgCat`. -/
@[simps! obj map]
private def commBialgCatToComonCommAlgCat : CommBialgCat R ⥤ (Mon_ (CommAlgCat R)ᵒᵖ)ᵒᵖ where
  obj A := .op {
    X := .op <| .of R A
    one := (CommAlgCat.ofHom <| counitAlgHom R A).op
    mul := (CommAlgCat.ofHom <| comulAlgHom R A).op
    one_mul := by ext; exact Coalgebra.rTensor_counit_comul _
    mul_one := by ext; exact Coalgebra.lTensor_counit_comul _
    mul_assoc := by ext; exact (Coalgebra.coassoc_symm_apply _).symm
  }
  map {A B} f := .op {
    hom := (CommAlgCat.ofHom f.hom).op
    one_hom := by ext; simp
    mul_hom := by
      ext
      simp only [unop_comp, Quiver.Hom.unop_op, CommAlgCat.hom_comp, CommAlgCat.hom_ofHom,
        CommAlgCat.tensorHom_unop_hom]
      rw [BialgHomClass.map_comp_comulAlgHom]
  }

/-- Implementation detail of `commBialgCatEquivComonCommAlg`. -/
@[simps! obj map]
private def comonCommAlgCatToCommBialgCat : (Mon_ (CommAlgCat R)ᵒᵖ)ᵒᵖ ⥤ CommBialgCat R where
  obj A := {
    carrier := A.unop.X.unop
    bialgebra := .ofAlgHom A.unop.mul.unop.hom A.unop.one.unop.hom
      congr(($((Mon_Class.mul_assoc_flip A.unop.X).symm)).unop.hom)
      congr(($(Mon_Class.one_mul A.unop.X)).unop.hom)
      congr(($(Mon_Class.mul_one A.unop.X)).unop.hom)
  }
  map {A B} f := CommBialgCat.ofHom <| .ofAlgHom f.unop.hom.unop.hom
    congr(($(IsMon_Hom.one_hom (f := f.unop.hom))).unop.hom.toLinearMap)
    congr(($((IsMon_Hom.mul_hom (f := f.unop.hom)).symm)).unop.hom.toLinearMap)

variable (R) in
/-- Commutative bialgebras over a commutative ring `R` are the same thing as comonoid
`R`-algebras. -/
@[simps!]
def commBialgCatEquivComonCommAlgCat : CommBialgCat R ≌ (Mon_ (CommAlgCat R)ᵒᵖ)ᵒᵖ where
  functor := commBialgCatToComonCommAlgCat
  inverse := comonCommAlgCatToCommBialgCat
  unitIso.hom := 𝟙 _
  unitIso.inv := 𝟙 _
  counitIso.hom := 𝟙 _
  counitIso.inv := 𝟙 _

instance isCommMon_commBialgCatEquivComonCommAlgCat_functor_obj_unop_X {A : CommBialgCat.{u} R}
    [IsCocomm R A] : IsCommMon ((commBialgCatEquivComonCommAlgCat R).functor.obj A).unop.X where
  mul_comm' := by
    ext : 2
    exact congr(AlgHomClass.toAlgHom ((commBialgCatEquivComonCommAlgCat R).functor.map <|
      CommBialgCat.ofHom $(comm_comp_comulBialgHom R A)).unop.hom.unop.hom)

end CategoryTheory
