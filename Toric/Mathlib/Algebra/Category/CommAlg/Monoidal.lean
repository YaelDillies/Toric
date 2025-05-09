/-
Copyright (c) 2025 Yaël Dillies, Christian Merten, Michał Mrugała, Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Christian Merten, Michał Mrugała, Andrew Yang
-/
import Mathlib.CategoryTheory.ChosenFiniteProducts
import Toric.Mathlib.Algebra.Category.CommAlg.Basic

/-!
# The cocartesian monoidal category structure on commutative `R`-algebras
-/

noncomputable section

open CategoryTheory Limits TensorProduct

namespace CommAlg
universe u v
variable {R : Type u} [CommRing R] (A B C : CommAlg.{u} R)

/-- The explicit cocone with tensor products as the fibered product in `CommAlg`. -/
def binaryCofan : BinaryCofan A B :=
  .mk (ofHom Algebra.TensorProduct.includeLeft)
    (ofHom (Algebra.TensorProduct.includeRight (A := A)))

@[simp]
lemma binaryCofan_inl : (binaryCofan A B).inl = ofHom Algebra.TensorProduct.includeLeft := rfl

@[simp]
lemma binaryCofan_inr : (binaryCofan A B).inr = ofHom Algebra.TensorProduct.includeRight := rfl

@[simp] lemma binaryCofan_pt : (binaryCofan A B).pt = .of R (A ⊗[R] B) := rfl

/-- Verify that the pushout cocone is indeed the colimit. -/
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

instance : ChosenFiniteProducts (CommAlg R)ᵒᵖ :=
  .ofChosenFiniteProducts ⟨_, terminalOpOfInitial isInitialSelf⟩ fun A B ↦
    ⟨BinaryCofan.op <| binaryCofan (unop A) (unop B),
      BinaryCofan.IsColimit.op <| binaryCofanIsColimit (unop A) (unop B)⟩

instance : BraidedCategory (CommAlg R)ᵒᵖ := .ofChosenFiniteProducts

open MonoidalCategory

variable {A B}

lemma rightWhisker_hom (f : A ⟶ B) :
    (f.op ▷ op C).unop.hom = Algebra.TensorProduct.map f.hom (.id _ _) := by
  suffices f.op ▷ op C = (ofHom (Algebra.TensorProduct.map f.hom (.id _ _))).op by
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
  suffices op C ◁ f.op = (ofHom (Algebra.TensorProduct.map (.id _ _) f.hom)).op by
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
      (ofHom (Algebra.TensorProduct.assoc R A B C).symm.toAlgHom).op by
    rw [this]; rfl
  ext <;> simp <;> rfl

variable {C} in
lemma associator_inv_unop_hom :
    (α_ (op A) (op B) (op C)).inv.unop.hom =
      (Algebra.TensorProduct.assoc R A B C).toAlgHom := by
  suffices (α_ (op A) (op B) (op C)).inv =
      (ofHom (Algebra.TensorProduct.assoc R A B C).toAlgHom).op by
    rw [this]; rfl
  ext <;> simp <;> rfl

variable {C} in
lemma tensorHom_unop_hom {D : CommAlg R} (f : A ⟶ C) (g : B ⟶ D) :
    (MonoidalCategoryStruct.tensorHom f.op g.op).unop.hom =
      (Algebra.TensorProduct.map f.hom g.hom) := by
  rw [MonoidalCategory.tensorHom_def]
  ext
  simp only [unop_comp, CommAlg.hom_comp, CommAlg.rightWhisker_hom, CommAlg.hom_ofHom,
    CommAlg.leftWhisker_hom]
  rw [← Algebra.TensorProduct.map_comp]
  simp

end CommAlg
