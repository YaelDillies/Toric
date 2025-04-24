/-
Copyright (c) 2025 Yaël Dillies, Michał Mrugała. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Michał Mrugała
-/
import Mathlib.Algebra.Category.AlgebraCat.Basic
import Mathlib.Algebra.Category.Ring.Under.Basic
import Mathlib.CategoryTheory.Monoidal.Grp_
import Mathlib.RingTheory.HopfAlgebra.Basic
import Toric.Mathlib.Algebra.Category.CommBialg
import Toric.Mathlib.RingTheory.Bialgebra.Equiv
import Toric.Mathlib.RingTheory.HopfAlgebra.Basic

/-!
# The category of commutative Hopf algebras over a commutative ring

This file defines the bundled category `CommHopfAlg` of commutative Hopf algebras over a fixed
commutative ring `R` along with the forgetful functor to `CommBialg`.
-/

noncomputable section

open CategoryTheory Limits HopfAlgebra

universe v u

variable {R : Type u} [CommRing R]

variable (R) in
/-- The category of commutative `R`-Hopf algebras and their morphisms. -/
structure CommHopfAlg where
  private mk ::
  /-- The underlying type. -/
  carrier : Type v
  [commRing : CommRing carrier]
  [hopfAlgebra : HopfAlgebra R carrier]

namespace CommHopfAlg
variable {A B C : CommHopfAlg.{v} R} {X Y Z : Type v} [CommRing X] [HopfAlgebra R X]
  [CommRing Y] [HopfAlgebra R Y] [CommRing Z] [HopfAlgebra R Z]

attribute [instance] commRing hopfAlgebra

initialize_simps_projections CommHopfAlg (-commRing, -hopfAlgebra)

instance : CoeSort (CommHopfAlg R) (Type v) := ⟨carrier⟩

attribute [coe] CommHopfAlg.carrier

variable (R) in
/-- Turn an unbundled `R`-Hopf algebra into the corresponding object in the category of
`R`-Hopf algebras.

This is the preferred way to construct a term of `CommHopfAlg R`. -/
abbrev of (X : Type v) [CommRing X] [HopfAlgebra R X] : CommHopfAlg.{v} R := ⟨X⟩

variable (R) in
lemma coe_of (X : Type v) [CommRing X] [HopfAlgebra R X] : (of R X : Type v) = X := rfl

/-- The type of morphisms in `CommBialg R`. -/
@[ext]
structure Hom (A B : CommHopfAlg.{v} R) where
  private mk ::
  /-- The underlying bialgebra map. -/
  hom' : A →ₐc[R] B

instance : Category (CommHopfAlg.{v} R) where
  Hom A B := Hom A B
  id A := ⟨.id R A⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

instance : ConcreteCategory (CommHopfAlg.{v} R) (· →ₐc[R] ·) where
  hom := Hom.hom'
  ofHom := Hom.mk

/-- Turn a morphism in `CommHopfAlg` back into a `BialgHom`. -/
abbrev Hom.hom (f : Hom A B) := ConcreteCategory.hom (C := CommHopfAlg R) f

/-- Typecheck a `BialgHom` as a morphism in `CommHopfAlg R`. -/
abbrev ofHom {_ : CommRing X} {_ : CommRing Y} {_ : HopfAlgebra R X} {_ : HopfAlgebra R Y}
    (f : X →ₐc[R] Y) : of R X ⟶ of R Y := ConcreteCategory.ofHom (C := CommHopfAlg R) f

/-- Use the `ConcreteCategory.hom` projection for `@[simps]` lemmas. -/
def Hom.Simps.hom (A B : CommHopfAlg.{v} R) (f : Hom A B) := f.hom

initialize_simps_projections Hom (hom' → hom)

/-!
The results below duplicate the `ConcreteCategory` simp lemmas, but we can keep them for `dsimp`.
-/

@[simp] lemma hom_id : (𝟙 A : A ⟶ A).hom = AlgHom.id R A := rfl

/- Provided for rewriting. -/
lemma id_apply (A : CommHopfAlg.{v} R) (a : A) : (𝟙 A : A ⟶ A) a = a := by simp

@[simp] lemma hom_comp (f : A ⟶ B) (g : B ⟶ C) : (f ≫ g).hom = g.hom.comp f.hom := rfl

/- Provided for rewriting. -/
lemma comp_apply (f : A ⟶ B) (g : B ⟶ C) (a : A) : (f ≫ g) a = g (f a) := by simp

@[simp] lemma hom_ofHom (f : X →ₐc[R] Y) : (ofHom f).hom = f := rfl
@[simp] lemma ofHom_hom (f : A ⟶ B) : ofHom f.hom = f := rfl

@[simp] lemma ofHom_id : ofHom (.id R X) = 𝟙 (of R X) := rfl

@[simp]
lemma ofHom_comp (f : X →ₐc[R] Y) (g : Y →ₐc[R] Z) : ofHom (g.comp f) = ofHom f ≫ ofHom g := rfl

lemma ofHom_apply (f : X →ₐc[R] Y) (x : X) : ofHom f x = f x := rfl

lemma inv_hom_apply (e : A ≅ B) (x : A) : e.inv (e.hom x) = x := by simp [← comp_apply]
lemma hom_inv_apply (e : A ≅ B) (x : B) : e.hom (e.inv x) = x := by simp [← comp_apply]

instance : Inhabited (CommHopfAlg R) := ⟨of R R⟩

lemma forget_obj (A : CommHopfAlg.{v} R) : (forget (CommHopfAlg.{v} R)).obj A = A := rfl

lemma forget_map (f : A ⟶ B) : (forget (CommHopfAlg.{v} R)).map f = f := rfl

instance : Ring ((forget (CommHopfAlg R)).obj A) := inferInstanceAs <| Ring A

instance : HopfAlgebra R ((forget (CommHopfAlg R)).obj A) := inferInstanceAs <| HopfAlgebra R A

instance hasForgetToCommBialg : HasForget₂ (CommHopfAlg.{v} R) (CommBialg.{v} R) where
  forget₂.obj A := .of R A
  forget₂.map f := CommBialg.ofHom f.hom

@[simp] lemma forget₂_commBialg_obj (A : CommHopfAlg.{v} R) :
    (forget₂ (CommHopfAlg.{v} R) (CommBialg.{v} R)).obj A = .of R A := rfl

@[simp] lemma forget₂_commBialg_map (f : A ⟶ B) :
    (forget₂ (CommHopfAlg.{v} R) (CommBialg.{v} R)).map f = CommBialg.ofHom f.hom := rfl

/-- Forgetting to the underlying type and then building the bundled object returns the original Hopf
algebra. -/
@[simps]
def ofSelfIso (A : CommHopfAlg.{v} R) : of R A ≅ A where
  hom := 𝟙 A
  inv := 𝟙 A

/-- Build an isomorphism in the category `CommHopfAlg R` from a `BialgEquiv` between
`HopfAlgebra`s. -/
@[simps]
def isoMk {X Y : Type v} {_ : CommRing X} {_ : CommRing Y} {_ : HopfAlgebra R X}
    {_ : HopfAlgebra R Y} (e : X ≃ₐc[R] Y) : of R X ≅ of R Y where
  hom := ofHom (e : X →ₐc[R] Y)
  inv := ofHom (e.symm : Y →ₐc[R] X)

/-- Build a `BialgEquiv` from an isomorphism in the category `CommHopfAlg R`. -/
@[simps]
def ofIso (i : A ≅ B) : A ≃ₐc[R] B where
  __ := i.hom.hom
  toFun := i.hom
  invFun := i.inv
  left_inv x := by simp
  right_inv x := by simp

/-- Commutative Hopf algebra equivalences between `HopfAlgebra`s are the same as (isomorphic to)
isomorphisms in `CommHopfAlg R`. -/
@[simps]
def isoEquivalgEquiv : (of R X ≅ of R Y) ≅ (X ≃ₐc[R] Y) where
  hom := ofIso
  inv := isoMk

instance reflectsIsomorphisms_forget_commHopfAlg :
    (forget (CommHopfAlg.{u} R)).ReflectsIsomorphisms where
  reflects {X Y} f _ := by
    let i := asIso ((forget (CommHopfAlg.{u} R)).map f)
    let e : X ≃ₐc[R] Y := { f.hom, i.toEquiv with }
    exact (isoMk e).isIso_hom

end CommHopfAlg

/-- Implementation detail of `commHopfAlgEquivCogrpCommAlg`. -/
@[simps! obj map]
private def commHopfAlgToCogrpAlg : CommHopfAlg R ⥤ (Grp_ (CommAlg R)ᵒᵖ)ᵒᵖ where
  obj A := .op {
    toMon_ := ((commBialgEquivComonCommAlg R).functor.obj <| .of R A).unop
    inv := (CommAlg.ofHom <| HopfAlgebra.antipodeAlgHom R A).op
    left_inv := by
      apply Quiver.Hom.unop_inj
      ext (x : A)
      refine .trans ?_ (HopfAlgebra.mul_antipode_rTensor_comul_apply (R := R) x)
      change (CartesianMonoidalCategory.lift (CommAlg.ofHom (HopfAlgebra.antipodeAlgHom R A)).op
        (𝟙 _)).unop.hom (CoalgebraStruct.comul (R := R) x) = _
      induction CoalgebraStruct.comul (R := R) x with
      | zero => simp
      | tmul x y => rfl
      | add x y _ _ => simp_all
    right_inv := by
      apply Quiver.Hom.unop_inj
      ext (x : A)
      refine .trans ?_ (HopfAlgebra.mul_antipode_lTensor_comul_apply (R := R) x)
      change (CartesianMonoidalCategory.lift (𝟙 _) (CommAlg.ofHom
        (HopfAlgebra.antipodeAlgHom R A)).op).unop.hom (CoalgebraStruct.comul (R := R) x) = _
      induction CoalgebraStruct.comul (R := R) x with
      | zero => simp
      | tmul x y => rfl
      | add x y _ _ => simp_all
  }
  map {A B} f := (commBialgEquivComonCommAlg R).functor.map (CommBialg.ofHom f.hom)

/-- Implementation detail of `commHopfAlgEquivCogrpCommAlg`. -/
@[simps! obj map]
private def cogrpAlgToCommHopfAlg : (Grp_ (CommAlg R)ᵒᵖ)ᵒᵖ ⥤ CommHopfAlg R where
  obj A := {
    __ := (commBialgEquivComonCommAlg R).inverse.obj <| .op A.unop.toMon_
    hopfAlgebra := {
      __ := ((commBialgEquivComonCommAlg R).inverse.obj <| .op A.unop.toMon_).bialgebra
      antipode := A.unop.inv.unop.hom.toLinearMap
      mul_antipode_rTensor_comul := by
        convert congr(($(Grp_Class.left_inv A.unop.X)).unop.hom.toLinearMap)
        simp [-Grp_Class.left_inv]
        rw [← LinearMap.comp_assoc]
        congr 1
        ext
        rfl
      mul_antipode_lTensor_comul := by
        convert congr(($(Grp_Class.right_inv A.unop.X)).unop.hom.toLinearMap)
        simp [-Grp_Class.right_inv]
        rw [← LinearMap.comp_assoc]
        congr 1
        ext
        rfl
    }
  }
  map {A B f} := CommHopfAlg.ofHom ((commBialgEquivComonCommAlg R).inverse.map <| .op f.unop).hom

variable (R) in
/-- Commutative Hopf algebras over a commutative ring `R` are the same thing as cogroup
`R`-algebras. -/
@[simps unitIso_inv counitIso_hom counitIso_inv]
def commHopfAlgEquivCogrpCommAlg : CommHopfAlg R ≌ (Grp_ (CommAlg R)ᵒᵖ)ᵒᵖ where
  functor := commHopfAlgToCogrpAlg
  inverse := cogrpAlgToCommHopfAlg
  unitIso.hom := 𝟙 _
  unitIso.inv := 𝟙 _
  counitIso.hom := 𝟙 _
  counitIso.inv := 𝟙 _
