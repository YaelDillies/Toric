/-
Copyright (c) 2025 Yaël Dillies, Christian Merten, Michał Mrugała, Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Christian Merten, Michał Mrugała, Andrew Yang
-/
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Toric.Mathlib.Algebra.Category.CommAlgCat.Basic

/-!
# The cocartesian monoidal category structure on commutative `R`-algebras
-/

noncomputable section

namespace CategoryTheory.CommAlgCat

open Limits TensorProduct
universe u v
variable {R : Type u} [CommRing R] {A B C : CommAlgCat.{u} R}

variable (A B) in
/-- The explicit cocone with tensor products as the fibered product in `CommAlgCat`. -/
def binaryCofan : BinaryCofan A B :=
  .mk (ofHom Algebra.TensorProduct.includeLeft)
    (ofHom (Algebra.TensorProduct.includeRight (A := A)))

variable (A B) in
@[simp]
lemma binaryCofan_inl : (binaryCofan A B).inl = ofHom Algebra.TensorProduct.includeLeft := rfl

variable (A B) in
@[simp]
lemma binaryCofan_inr : (binaryCofan A B).inr = ofHom Algebra.TensorProduct.includeRight := rfl

variable (A B) in
@[simp] lemma binaryCofan_pt : (binaryCofan A B).pt = .of R (A ⊗[R] B) := rfl

variable (A B) in
/-- Verify that the pushout cocone is indeed the colimit. -/
def binaryCofanIsColimit : IsColimit (binaryCofan A B) :=
  BinaryCofan.IsColimit.mk _
    (fun f g ↦ ofHom (Algebra.TensorProduct.lift f.hom g.hom fun _ _ ↦ .all _ _))
    (fun f g ↦ by ext1; exact Algebra.TensorProduct.lift_comp_includeLeft _ _ fun _ _ ↦ .all _ _)
    (fun f g ↦ by ext1; exact Algebra.TensorProduct.lift_comp_includeRight _ _ fun _ _ ↦ .all _ _)
    (fun f g m hm₁ hm₂ ↦ by
      ext1
      refine Algebra.TensorProduct.liftEquiv.symm_apply_eq (y := ⟨⟨_, _⟩, fun _ _ ↦ .all _ _⟩).mp ?_
      exact Subtype.ext (Prod.ext congr(($hm₁).hom) congr(($hm₂).hom)))

def isInitialSelf : IsInitial (of R R) := .ofUniqueHom (fun A ↦ ofHom (Algebra.ofId R A))
  fun _ _ ↦ hom_ext (Algebra.ext_id _ _ _)

open Opposite Algebra.TensorProduct CommAlgCat

attribute [local ext] Quiver.Hom.unop_inj

instance : MonoidalCategory (CommAlgCat.{u} R)ᵒᵖ where
  tensorObj S T := op <| of R (S.unop ⊗[R] T.unop)
  whiskerLeft S {T₁ T₂} f := .op <| ofHom (Algebra.TensorProduct.map (.id _ _) f.unop.hom)
  whiskerRight {S₁ S₂} f T := .op <| ofHom (Algebra.TensorProduct.map f.unop.hom (.id _ _))
  tensorHom {S₁ S₂ T₁ T₂} f g := .op <| ofHom (map f.unop.hom g.unop.hom)
  tensorUnit := .op (.of R R)
  associator {S T U} := .op <| isoMk (Algebra.TensorProduct.assoc R R _ _ _).symm
  leftUnitor S := .op <| isoMk (Algebra.TensorProduct.lid R _).symm
  rightUnitor _ := .op <| isoMk (Algebra.TensorProduct.rid R R _).symm
  tensorHom_def := by intros; ext <;> rfl
  tensor_id := by intros; ext <;> rfl
  tensor_comp := by intros; ext <;> rfl
  whiskerLeft_id := by intros; ext <;> rfl
  id_whiskerRight := by intros; ext <;> rfl
  associator_naturality := by intros; ext <;> rfl
  leftUnitor_naturality := by intros; rfl
  rightUnitor_naturality := by intros; rfl
  pentagon := by intros; ext <;> rfl
  triangle := by intros; ext <;> rfl

instance : CartesianMonoidalCategory (CommAlgCat.{u} R)ᵒᵖ where
  isTerminalTensorUnit := terminalOpOfInitial isInitialSelf
  fst := _
  snd := _
  tensorProductIsBinaryProduct S T :=
    BinaryCofan.IsColimit.op <| binaryCofanIsColimit (unop S) (unop T)
  fst_def S T := by ext x; show x ⊗ₜ 1 = x ⊗ₜ algebraMap R (unop T:) 1; simp
  snd_def S T := by ext x; show 1 ⊗ₜ x = algebraMap R (unop S:) 1 ⊗ₜ x; simp

instance : BraidedCategory (CommAlgCat.{u} R)ᵒᵖ where
  braiding S T := .op <| isoMk (Algebra.TensorProduct.comm R _ _)
  braiding_naturality_right := by intros; ext <;> rfl
  braiding_naturality_left := by intros; ext <;> rfl
  hexagon_forward S T U := by ext <;> rfl
  hexagon_reverse S T U := by ext <;> rfl

open MonoidalCategory

@[simp] lemma rightWhisker_hom (f : A ⟶ B) :
    (f.op ▷ op C).unop.hom = Algebra.TensorProduct.map f.hom (.id _ _) := rfl

@[simp] lemma leftWhisker_hom (f : A ⟶ B) :
    (op C ◁ f.op).unop.hom = Algebra.TensorProduct.map (.id _ _) f.hom := rfl

@[simp] lemma associator_hom_unop_hom :
    (α_ (op A) (op B) (op C)).hom.unop.hom =
      (Algebra.TensorProduct.assoc R R A B C).symm.toAlgHom := rfl

@[simp] lemma associator_inv_unop_hom :
    (α_ (op A) (op B) (op C)).inv.unop.hom = (Algebra.TensorProduct.assoc R R A B C).toAlgHom := rfl

@[simp] lemma tensorHom_unop_hom {D : CommAlgCat R} (f : A ⟶ C) (g : B ⟶ D) :
    (f.op ⊗ g.op).unop.hom = Algebra.TensorProduct.map f.hom g.hom := rfl

end CategoryTheory.CommAlgCat
