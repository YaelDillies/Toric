/-
Copyright (c) 2025 Yaël Dillies, Christian Merten, Michał Mrugała, Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Christian Merten, Michał Mrugała, Andrew Yang
-/
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.CategoryTheory.ChosenFiniteProducts
import Mathlib.RingTheory.TensorProduct.Basic
import Toric.Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts

/-!
# Category of commutative algebras over a commutative ring

We introduce the bundled category `CommAlg` of algebras over a fixed commutative ring `R` along
with the forgetful functors to `RingCat` and `ModuleCat`. We furthermore show that the functor
associating to a type the free `R`-algebra on that type is left adjoint to the forgetful functor.
-/

open CategoryTheory Limits

universe v u

variable {R : Type u} [CommRing R]

variable (R) in
/-- The category of R-algebras and their morphisms. -/
structure CommAlg where
  private mk ::
  /-- The underlying type. -/
  carrier : Type v
  [isRing : CommRing carrier]
  [isAlgebra : Algebra R carrier]

attribute [instance] CommAlg.isRing CommAlg.isAlgebra

initialize_simps_projections CommAlg (-isRing, -isAlgebra)

namespace CommAlg
variable {A B C : CommAlg.{v} R}

instance : CoeSort (CommAlg R) (Type v) := ⟨CommAlg.carrier⟩

attribute [coe] CommAlg.carrier

variable (R) in
/-- The object in the category of R-algebras associated to a type equipped with the appropriate
typeclasses. This is the preferred way to construct a term of `CommAlg R`. -/
abbrev of (X : Type v) [CommRing X] [Algebra R X] : CommAlg.{v} R := ⟨X⟩

variable (R) in
lemma coe_of (X : Type v) [CommRing X] [Algebra R X] : (of R X : Type v) = X := rfl

/-- The type of morphisms in `CommAlg R`. -/
@[ext]
structure Hom (A B : CommAlg.{v} R) where
  private mk ::
  /-- The underlying algebra map. -/
  hom' : A →ₐ[R] B

instance : Category (CommAlg.{v} R) where
  Hom A B := Hom A B
  id A := ⟨AlgHom.id R A⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

instance : ConcreteCategory (CommAlg.{v} R) (· →ₐ[R] ·) where
  hom := Hom.hom'
  ofHom := Hom.mk

/-- Turn a morphism in `CommAlg` back into an `AlgHom`. -/
abbrev Hom.hom {A B : CommAlg.{v} R} (f : Hom A B) :=
  ConcreteCategory.hom (C := CommAlg R) f

/-- Typecheck an `AlgHom` as a morphism in `CommAlg`. -/
abbrev ofHom {A B : Type v} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B] (f : A →ₐ[R] B) :
    of R A ⟶ of R B :=
  ConcreteCategory.ofHom (C := CommAlg R) f

/-- Use the `ConcreteCategory.hom` projection for `@[simps]` lemmas. -/
def Hom.Simps.hom (A B : CommAlg.{v} R) (f : Hom A B) := f.hom

initialize_simps_projections Hom (hom' → hom)

/-!
The results below duplicate the `ConcreteCategory` simp lemmas, but we can keep them for `dsimp`.
-/

@[simp] lemma hom_id {A : CommAlg.{v} R} : (𝟙 A : A ⟶ A).hom = AlgHom.id R A := rfl

/- Provided for rewriting. -/
lemma id_apply (A : CommAlg.{v} R) (a : A) : (𝟙 A : A ⟶ A) a = a := by simp

@[simp] lemma hom_comp (f : A ⟶ B) (g : B ⟶ C) : (f ≫ g).hom = g.hom.comp f.hom := rfl

/- Provided for rewriting. -/
lemma comp_apply (f : A ⟶ B) (g : B ⟶ C) (a : A) : (f ≫ g) a = g (f a) := by simp

@[ext] lemma hom_ext {f g : A ⟶ B} (hf : f.hom = g.hom) : f = g := Hom.ext hf

@[simp]
lemma hom_ofHom {X Y : Type v} [CommRing X] [Algebra R X] [CommRing Y] [Algebra R Y]
    (f : X →ₐ[R] Y) : (ofHom f).hom = f := rfl

@[simp] lemma ofHom_hom (f : A ⟶ B) : ofHom (Hom.hom f) = f := rfl

@[simp]
lemma ofHom_id {X : Type v} [CommRing X] [Algebra R X] : ofHom (AlgHom.id R X) = 𝟙 (of R X) := rfl

@[simp]
lemma ofHom_comp {X Y Z : Type v} [CommRing X] [CommRing Y] [CommRing Z] [Algebra R X] [Algebra R Y]
    [Algebra R Z] (f : X →ₐ[R] Y) (g : Y →ₐ[R] Z) :
    ofHom (g.comp f) = ofHom f ≫ ofHom g := rfl

lemma ofHom_apply {X Y : Type v} [CommRing X] [Algebra R X] [CommRing Y] [Algebra R Y]
    (f : X →ₐ[R] Y) (x : X) : ofHom f x = f x := rfl

lemma inv_hom_apply (e : A ≅ B) (x : A) : e.inv (e.hom x) = x := by simp [← comp_apply]

lemma hom_inv_apply (e : A ≅ B) (x : B) : e.hom (e.inv x) = x := by simp [← comp_apply]

instance : Inhabited (CommAlg R) := ⟨of R R⟩

lemma forget_obj (A : CommAlg.{v} R) : (forget (CommAlg.{v} R)).obj A = A := rfl

lemma forget_map (f : A ⟶ B) : (forget (CommAlg.{v} R)).map f = f := rfl

instance {S : CommAlg.{v} R} : Ring ((forget (CommAlg R)).obj S) :=
  inferInstanceAs <| Ring S.carrier

instance {S : CommAlg.{v} R} : Algebra R ((forget (CommAlg R)).obj S) :=
  inferInstanceAs <| Algebra R S.carrier

instance hasForgetToRing : HasForget₂ (CommAlg.{v} R) RingCat.{v} where
  forget₂.obj A := RingCat.of A
  forget₂.map f := RingCat.ofHom f.hom.toRingHom

instance hasForgetToModule : HasForget₂ (CommAlg.{v} R) (ModuleCat.{v} R) where
  forget₂.obj M := ModuleCat.of R M
  forget₂.map f := ModuleCat.ofHom f.hom.toLinearMap

@[simp]
lemma forget₂_module_obj (X : CommAlg.{v} R) :
    (forget₂ (CommAlg.{v} R) (ModuleCat.{v} R)).obj X = ModuleCat.of R X := rfl

@[simp]
lemma forget₂_module_map {X Y : CommAlg.{v} R} (f : X ⟶ Y) :
    (forget₂ (CommAlg.{v} R) (ModuleCat.{v} R)).map f = ModuleCat.ofHom f.hom.toLinearMap := rfl

/-- Forgetting to the underlying type and then building the bundled object returns the original
algebra. -/
@[simps]
def ofSelfIso (M : CommAlg.{v} R) : CommAlg.of R M ≅ M where
  hom := 𝟙 M
  inv := 𝟙 M

end CommAlg

variable {X₁ X₂ : Type u}

/-- Build an isomorphism in the category `CommAlg R` from a `AlgEquiv` between `Algebra`s. -/
@[simps]
def AlgEquiv.toCommAlgIso
    {g₁ : CommRing X₁} {g₂ : CommRing X₂} {m₁ : Algebra R X₁} {m₂ : Algebra R X₂}
    (e : X₁ ≃ₐ[R] X₂) : CommAlg.of R X₁ ≅ CommAlg.of R X₂ where
  hom := CommAlg.ofHom (e : X₁ →ₐ[R] X₂)
  inv := CommAlg.ofHom (e.symm : X₂ →ₐ[R] X₁)

namespace CategoryTheory.Iso

/-- Build a `AlgEquiv` from an isomorphism in the category `CommAlg R`. -/
@[simps]
def commAlgIsoToAlgEquiv {X Y : CommAlg R} (i : X ≅ Y) : X ≃ₐ[R] Y where
  __ := i.hom.hom
  toFun := i.hom
  invFun := i.inv
  left_inv x := by simp
  right_inv x := by simp

end CategoryTheory.Iso

/-- Algebra equivalences between `Algebra`s are the same as (isomorphic to) isomorphisms in
`CommAlg`. -/
@[simps]
def algEquivIsoCommAlgIso {X Y : Type u} [CommRing X] [CommRing Y] [Algebra R X] [Algebra R Y] :
    (X ≃ₐ[R] Y) ≅ CommAlg.of R X ≅ CommAlg.of R Y where
  hom e := e.toCommAlgIso
  inv i := i.commAlgIsoToAlgEquiv

instance CommAlg.forget_reflects_isos : (forget (CommAlg.{u} R)).ReflectsIsomorphisms where
  reflects {X Y} f _ := by
    let i := asIso ((forget (CommAlg.{u} R)).map f)
    let e : X ≃ₐ[R] Y := { f.hom, i.toEquiv with }
    exact e.toCommAlgIso.isIso_hom

namespace CommAlg

noncomputable section Coprod

open TensorProduct

variable (A B C : CommAlg R)

/-- The explicit cocone with tensor products as the fibered product in `CommRingCat`. -/
def binaryCofan : Limits.BinaryCofan A B :=
  Limits.BinaryCofan.mk (ofHom Algebra.TensorProduct.includeLeft)
    (ofHom (Algebra.TensorProduct.includeRight (R := R) (A := A)))

@[simp]
lemma binaryCofan_inl : (binaryCofan A B).inl = ofHom Algebra.TensorProduct.includeLeft := rfl

@[simp]
lemma binaryCofan_inr : (binaryCofan A B).inr = ofHom Algebra.TensorProduct.includeRight := rfl

@[simp] lemma binaryCofan_pt : (binaryCofan A B).pt = .of R (A ⊗[R] B) := rfl

/-- Verify that the `pushout_cocone` is indeed the colimit. -/
def binaryCofanIsColimit : Limits.IsColimit (binaryCofan A B) :=
  Limits.BinaryCofan.IsColimit.mk _
    (fun f g ↦ ofHom (Algebra.TensorProduct.lift f.hom g.hom fun _ _ ↦ .all _ _))
    (fun f g ↦ by ext1; exact Algebra.TensorProduct.lift_comp_includeLeft _ _ fun _ _ ↦ .all _ _)
    (fun f g ↦ by ext1; exact Algebra.TensorProduct.lift_comp_includeRight _ _ fun _ _ ↦ .all _ _)
    (fun f g m hm₁ hm₂ ↦ by
      ext1
      refine Algebra.TensorProduct.liftEquiv.symm_apply_eq (y := ⟨⟨_, _⟩, fun _ _ ↦ .all _ _⟩).mp ?_
      exact Subtype.ext (Prod.ext congr(($hm₁).hom) congr(($hm₂).hom)))

def isInitialSelf : Limits.IsInitial (of R R) := .ofUniqueHom (fun A ↦ ofHom (Algebra.ofId R A))
  fun _ _ ↦ hom_ext (Algebra.ext_id _ _ _)

open Opposite

instance : ChosenFiniteProducts (CommAlg R)ᵒᵖ where
  product A B := ⟨BinaryCofan.op <| (binaryCofan (unop A) (unop B)),
    BinaryCofan.IsColimit.op <| (binaryCofanIsColimit (unop A) (unop B))⟩
  terminal := ⟨_, terminalOpOfInitial isInitialSelf⟩

open MonoidalCategory

variable {A B}

lemma rightWhisker_hom (f : A ⟶ B) :
    (f.op ▷ op C).unop.hom = Algebra.TensorProduct.map f.hom (.id _ _) := by
  suffices f.op ▷ op C = (CommAlg.ofHom (Algebra.TensorProduct.map f.hom (.id _ _))).op by
    rw [this]; rfl
  ext
  · simp
    rfl
  simp only [ChosenFiniteProducts.whiskerRight_snd]
  apply Quiver.Hom.unop_inj
  ext x
  show 1 ⊗ₜ[R] x = f 1 ⊗ₜ[R] x
  simp

lemma leftWhisker_hom (f : A ⟶ B) :
    (op C ◁ f.op).unop.hom = Algebra.TensorProduct.map (.id _ _) f.hom := by
  suffices op C ◁ f.op = (CommAlg.ofHom (Algebra.TensorProduct.map (.id _ _) f.hom)).op by
    rw [this]; rfl
  ext
  swap
  · simp
    rfl
  simp only [ChosenFiniteProducts.whiskerLeft_fst]
  apply Quiver.Hom.unop_inj
  ext x
  show x ⊗ₜ[R] 1 = x ⊗ₜ[R] f 1
  simp

variable {C} in
lemma associator_hom_unop_hom :
    (α_ (op A) (op B) (op C)).hom.unop.hom =
      (Algebra.TensorProduct.assoc R A B C).symm.toAlgHom := by
  suffices (α_ (op A) (op B) (op C)).hom =
      (CommAlg.ofHom (Algebra.TensorProduct.assoc R A B C).symm.toAlgHom).op by
    rw [this]; rfl
  ext <;> simp <;> rfl

variable {C} in
lemma associator_inv_unop_hom :
    (α_ (op A) (op B) (op C)).inv.unop.hom =
      (Algebra.TensorProduct.assoc R A B C).toAlgHom := by
  suffices (α_ (op A) (op B) (op C)).inv =
      (CommAlg.ofHom (Algebra.TensorProduct.assoc R A B C).toAlgHom).op by
    rw [this]; rfl
  ext <;> simp <;> rfl

end Coprod

end CommAlg


section

open MonoidalCategory

variable {R : Type*} [CommRing R] {A B C : (CommAlg R)ᵒᵖ}

example :
    (α_ A B C).inv.unop.hom =
      (Algebra.TensorProduct.assoc R A.unop B.unop C.unop).toAlgHom :=
  CommAlg.associator_inv_unop_hom

end
