/-
Copyright (c) 2025 Yaël Dillies, Christian Merten, Michał Mrugała, Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Christian Merten, Michał Mrugała, Andrew Yang
-/
import Mathlib.Algebra.Category.AlgebraCat.Basic
import Mathlib.Algebra.Category.Ring.Under.Basic
import Mathlib.CategoryTheory.Monoidal.Grp_
import Mathlib.RingTheory.HopfAlgebra.Basic
import Toric.Mathlib.Algebra.Category.CommBialg
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

instance : Category (CommHopfAlg.{v} R) where
  Hom A B := CommBialg.of R A ⟶ .of R B
  id A := 𝟙 <| CommBialg.of R A
  comp f g := f ≫ g

instance : ConcreteCategory (CommHopfAlg.{v} R) (· →ₐc[R] ·) where
  hom f := f.hom
  ofHom := CommBialg.ofHom

/-- Typecheck a `BialgHom` as a morphism in `CommHopfAlg R`. -/
abbrev ofHom (f : X →ₐc[R] Y) : of R X ⟶ of R Y := ConcreteCategory.ofHom (C := CommHopfAlg R) f

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
  -- TODO: We're missing `BialgEquiv` simp lemmas. Investigate how `CommAlg` does it.
  hom_inv_id := sorry
  inv_hom_id := sorry

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

variable (R) in
/-- Commutative Hopf algebras over a commutative ring `R` are the same thing as cogroup
`R`-algebras. -/
@[simps!]
def commHopfAlgEquivCogrpAlg : CommHopfAlg R ≌ (Grp_ (CommAlg R)ᵒᵖ)ᵒᵖ where
  functor.obj A := .op <| {
      toMon_ := ((commBialgEquivComonAlg R).functor.obj <| .of R A).unop
      inv := (CommAlg.ofHom <| HopfAlgebra.antipodeAlgHom R A).op
      left_inv := sorry
      right_inv := sorry
    }
  functor.map {A B} f := (commBialgEquivComonAlg R).functor.map f
  inverse.obj A := {
    __ := (commBialgEquivComonAlg R).inverse.obj <| .op A.unop.toMon_
    hopfAlgebra := {
      __ := ((commBialgEquivComonAlg R).inverse.obj <| .op A.unop.toMon_).bialgebra
      antipode := A.unop.inv.unop.hom.toLinearMap
      mul_antipode_rTensor_comul := sorry
      mul_antipode_lTensor_comul := sorry
    }
  }
  inverse.map {A B f} := (commBialgEquivComonAlg R).inverse.map <| .op f.unop
  unitIso := sorry
  counitIso := sorry
  functor_unitIso_comp := sorry
