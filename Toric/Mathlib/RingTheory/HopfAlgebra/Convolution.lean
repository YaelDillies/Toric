/-
Copyright (c) 2025 Yaël Dillies, Michał Mrugała, Yunzhou Xie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Michał Mrugała, Yunzhou Xie
-/
import Toric.Mathlib.Algebra.Algebra.Defs
import Toric.Mathlib.RingTheory.Bialgebra.Convolution
import Toric.Mathlib.RingTheory.HopfAlgebra.Basic
import Toric.Mathlib.RingTheory.TensorProduct.Basic

/-!
# Convolution product on Hopf algebra maps

This file constructs the ring structure on bialgebra homs `C → A` where `C` and `A` are Hopf
algebras and multiplication is given by
```
         .
        / \
f * g = f g
        \ /
         .
```
-/

suppress_compilation

open Algebra Coalgebra Bialgebra TensorProduct

variable {R A B₁ B₂ C : Type*} [CommSemiring R]

namespace HopfAlgebra

variable [CommSemiring A] [HopfAlgebra R A]

lemma antipode_mul_antidistrib (a b : A) :
    antipode R (a * b) = antipode R b * antipode R a := by
  let α := antipode R ∘ₗ .mul' R A
  let β : A ⊗[R] A →ₗ[R] A := .mul' R A ∘ₗ map (antipode R) (antipode R) ∘ₗ TensorProduct.comm R A A
  suffices α = β from congr($this (a ⊗ₜ b))
  apply left_inv_eq_right_inv (a := LinearMap.mul' R A) <;> ext a b
  · simp [α, ((ℛ R a).tmul (ℛ R b)).mul_apply, ← Bialgebra.counit_mul, mul_comm b a,
      ((ℛ R a).mul (ℛ R b)).algebraMap_counit_eq_sum_antipode_mul]
  · simp [((ℛ R a).tmul (ℛ R b)).mul_apply, mul_comm, mul_mul_mul_comm,
      Finset.sum_mul_sum, ← Finset.sum_product', α, β, -sum_mul_antipode_eq,
      (ℛ R a).algebraMap_counit_eq_sum_mul_antipode, (ℛ R b).algebraMap_counit_eq_sum_mul_antipode]

lemma antipode_mul_distrib (a b : A) :
    antipode R (a * b) = antipode R a * antipode R b := by
  rw [antipode_mul_antidistrib, mul_comm]

alias antipode_mul := antipode_mul_distrib

variable (R A) in
@[simps!]
def antipodeAlgHom : A →ₐ[R] A := .ofLinearMap (antipode R) antipode_one antipode_mul

@[simp] lemma toLinearMap_antipodeAlgHom : (antipodeAlgHom R A).toLinearMap = antipode R := rfl

end HopfAlgebra

namespace LinearMap

local notation "η" => Algebra.linearMap R A
local notation "ε" => counit (R := R) (A := C)
local notation "μ" => mul' R A
local notation "δ" => comul
local infix:70 " ⊗ₘ " => TensorProduct.map
-- local notation "α" => TensorProduct.assoc _ _ _

variable [Semiring C] [HopfAlgebra R C]

@[simp] lemma antipode_mul_id : antipode R (A := C) * id = 1 := by
  ext; simp [mul_def, ← LinearMap.rTensor_def]

@[simp] lemma id_mul_antipode : id * antipode R (A := C) = 1 := by
  ext; simp [mul_def, ← LinearMap.lTensor_def]

instance : Invertible (LinearMap.id (R := R) (M := C)) :=
  ⟨antipode R, antipode_mul_id, id_mul_antipode⟩

@[simp] lemma counit_comp_antipode : ε ∘ₗ antipode R (A := C) = ε := calc
  _ = 1 * (ε ∘ₗ antipode R (A := C)) := (one_mul _).symm
  _ = (ε ∘ₗ id) * (ε ∘ₗ antipode R (A := C)) := rfl
  _ = (counitAlgHom R C).toLinearMap ∘ₗ (id * antipode R (A := C)) := by
    simp only [comp_id, comp_mul_distrib]
    simp
  _ = ε ∘ₗ 1 := by simp
  _ = ε := by ext; simp

@[simp] lemma counit_antipode (a : C) : ε (antipode R a) = ε a := congr($counit_comp_antipode a)

end LinearMap

namespace LinearMap
variable [Semiring C] [HopfAlgebra R C]

local notation "ε₁" => counit (R := R) (A := C)
local notation "ε₂" => counit (R := R) (A := C ⊗[R] C)
local notation "μ₁" => LinearMap.mul' R C
local notation "μ₂" => LinearMap.mul' R (C ⊗[R] C)
local notation "δ₁" => comul (R := R) (A := C)
local notation "δ₂" => comul (R := R) (A := C ⊗[R] C)
local notation "η₁" => Algebra.linearMap R C
local notation "η₂" => Algebra.linearMap R (C ⊗[R] C)
local infix:90 " ◁ " => LinearMap.lTensor
local notation:90 f:90 " ▷ " X:90 => LinearMap.rTensor X f
local infix:70 " ⊗ₘ " => TensorProduct.map
local notation "α" => TensorProduct.assoc R
local notation "β" => TensorProduct.comm R
local notation "𝑺" => antipode R (A := C)
local notation "𝑭" => δ₁ ∘ₗ 𝑺
local notation "𝑮" => (𝑺 ⊗ₘ 𝑺) ∘ₗ (β C C) ∘ₗ δ₁

lemma comul_right_inv : δ₁ * 𝑭 = 1 := calc
    μ₂ ∘ₗ (δ₁ ⊗ₘ (δ₁ ∘ₗ 𝑺)) ∘ₗ δ₁
  _ = μ₂ ∘ₗ ((δ₁ ∘ₗ id) ⊗ₘ (δ₁ ∘ₗ 𝑺)) ∘ₗ δ₁ := rfl
  _ = μ₂ ∘ₗ (δ₁ ⊗ₘ δ₁) ∘ₗ (id ⊗ₘ 𝑺) ∘ₗ δ₁ := by
    simp only [_root_.TensorProduct.map_comp, comp_assoc]
  _ = δ₁ ∘ₗ μ₁ ∘ₗ (id ⊗ₘ 𝑺) ∘ₗ δ₁ := by
      have : μ₂ ∘ₗ (δ₁ ⊗ₘ δ₁) = δ₁ ∘ₗ μ₁ := by ext; simp
      simp [this, ← comp_assoc]
  _ = δ₁ ∘ₗ (id * 𝑺) := rfl
  _ = δ₁ ∘ₗ η₁ ∘ₗ ε₁ := by simp [one_def]
  _ = η₂ ∘ₗ ε₁ := by
      have : δ₁ ∘ₗ η₁ = η₂ := by ext; simp; rfl
      simp [this, ← comp_assoc]

end LinearMap

namespace AlgHom

variable [Semiring A] [Semiring C] [Algebra R A]
  [CommSemiring B₁] [CommSemiring B₂] [Algebra R B₁] [Algebra R B₂] [HopfAlgebra R C]

-- noncomputable
-- instance : Group (C →ₐ[R] B₁) where
--   inv f := (f.comp <| HopfAlgebra.antipodeAlgHom R C)
--   inv_mul_cancel l := by
--     ext x
--     dsimp [AlgHom.one_def, AlgHom.mul_def, Algebra.ofId]
--     trans l (algebraMap R C (counit x))
--     · rw [← HopfAlgebra.mul_antipode_rTensor_comul_apply]
--       induction comul (R := R) x with
--       | zero => simp
--       | add x y _ _ => simp [*]
--       | tmul x y => simp
--     · simp

-- lemma _root_.Bialgebra.comulAlgHom_def : Bialgebra.comulAlgHom R C =
--     Algebra.TensorProduct.includeLeft * Algebra.TensorProduct.includeRight := by
--   ext x
--   simp only [comulAlgHom_apply, AlgHom.mul_def, AlgHom.coe_comp, Function.comp_apply]
--   induction comul (R := R) x with
--   | zero => simp
--   | add x y hx hy => simp only [map_add, ← hx, ← hy]
--   | tmul x y => simp

-- lemma _root_.HopfAlgebra.antipodeAlgHom_def :
--     HopfAlgebra.antipodeAlgHom R C = (AlgHom.id _ _)⁻¹ := rfl

lemma _root_.Bialgebra.counitAlgHom_def :
    Bialgebra.counitAlgHom R C = 1 := rfl

lemma _root_.Bialgebra.counit_def :
    Coalgebra.counit (R := R) (A := C) = 1 := rfl

lemma _root_.Bialgebra.comul_def : Coalgebra.comul (R := R) (A := C) =
    Algebra.TensorProduct.includeLeft.toLinearMap *
    Algebra.TensorProduct.includeRight.toLinearMap := by
  ext x
  simp only [LinearMap.mul_apply]
  induction comul (R := R) x with
  | zero => simp
  | add x y hx hy => simp only [map_add, ← hx, ← hy]
  | tmul x y => simp

@[simps]
noncomputable
instance invertibleToLinearMap (f : C →ₐ[R] A) : Invertible f.toLinearMap := by
  refine ⟨f ∘ₗ antipode R, ?_, ?_⟩
  · ext x
    dsimp [AlgHom.one_def, AlgHom.mul_def, Algebra.ofId]
    trans f (algebraMap R C (counit x))
    · rw [← HopfAlgebra.mul_antipode_rTensor_comul_apply]
      induction comul (R := R) x with
      | zero => simp
      | add x y _ _ => simp [*]
      | tmul x y => simp
    · simp
  · ext x
    dsimp [AlgHom.one_def, AlgHom.mul_def, Algebra.ofId]
    trans f (algebraMap R C (counit x))
    · rw [← HopfAlgebra.mul_antipode_lTensor_comul_apply]
      induction comul (R := R) x with
      | zero => simp
      | add x y _ _ => simp [*]
      | tmul x y => simp
    · simp

lemma comul_antipode_inv : (comul ∘ₗ antipode R (A := C)) * comul = 1 := by
  ext x
  simp only [LinearMap.mul_apply, LinearMap.one_apply, Algebra.TensorProduct.algebraMap_apply]
  trans comul ((algebraMap R C) (counit x))
  · rw [← HopfAlgebra.mul_antipode_rTensor_comul_apply, ← LinearMap.rTensor_comp_lTensor,
      LinearMap.coe_comp, Function.comp_apply]
    induction comul (R := R) x with
    | zero => simp
    | add x y _ _ => simp_all [add_tmul]
    | tmul x y =>
      simp [LinearMap.rTensor_tmul, LinearMap.lTensor_tmul, LinearMap.mul'_apply]
  · simp

lemma _root_.HopfAlgebra.antipode_comul_antidistrib : comul ∘ₗ antipode R (A := C) =
    map (antipode R) (antipode R) ∘ₗ (Algebra.TensorProduct.comm R C C).toAlgHom.toLinearMap
       ∘ₗ comul := by
  let e :=
    (invertibleToLinearMap (Algebra.TensorProduct.includeLeft : C →ₐ[R] C ⊗[R] C)).mul
    (invertibleToLinearMap (Algebra.TensorProduct.includeRight : C →ₐ[R] C ⊗[R] C))
  have H : (comul ∘ₗ antipode R (A := C)) * comul = 1 := comul_antipode_inv
  nth_rw 2 [Bialgebra.comul_def] at H
  convert (invOf_eq_left_inv H).symm
  simp only [AlgEquiv.toAlgHom_eq_coe, AlgEquiv.toAlgHom_toLinearMap, invOf_mul,
    invertibleToLinearMap_invOf]
  simp only [LinearMap.mul_def, ← LinearMap.comp_assoc]
  congr 1
  ext; simp

end AlgHom

namespace HopfAlgebra
variable {C : Type*} [Semiring C] [HopfAlgebra R C] [IsCocomm R C]

lemma _root_.HopfAlgebra.antipode_comul_distrib : comul ∘ₗ antipode R (A := C) =
    map (antipode R) (antipode R) ∘ₗ comul := by
  simp [antipode_comul_antidistrib]

variable (R C) in
/-- The antipode as a coalgebra hom. -/
def antipodeCoalgHom : C →ₗc[R] C where
  __ := antipode R (A := C)
  counit_comp := by ext a; exact antipode_counit _
  map_comp_comul := antipode_comul_distrib.symm

@[simp]
lemma antipodeCoalgHom_def : antipodeCoalgHom R C = antipode R (A := C) := rfl

variable (R A) in
/-- The antipode as a bialgebra hom. -/
def antipodeBialgHom [CommSemiring A] [HopfAlgebra R A] [IsCocomm R A] : A →ₐc[R] A where
  __ := antipodeCoalgHom R A
  map_one' := antipode_one
  map_mul' := antipode_mul_distrib

end HopfAlgebra

namespace AlgHom
variable [CommSemiring A] [Semiring C] [Bialgebra R C] [HopfAlgebra R A]

lemma antipode_id_cancel : HopfAlgebra.antipodeAlgHom R A * AlgHom.id R A = 1 := by
  apply AlgHom.toLinearMap_injective
  rw [toLinearMap_mul]
  ext
  simp [LinearMap.antipode_mul_id]

lemma counit_comp_antipode :
    (counitAlgHom R A).comp (HopfAlgebra.antipodeAlgHom R A) = counitAlgHom R A := by
  apply AlgHom.toLinearMap_injective
  simp [LinearMap.counit_comp_antipode]

private lemma inv_convMul_cancel (f : C →ₐc[R] A) :
    (.comp (HopfAlgebra.antipodeAlgHom R A) f : C →ₐ[R] A) * f = 1 := calc
  _ = (.comp (HopfAlgebra.antipodeAlgHom R A) f : C →ₐ[R] A) * (.comp (.id R A) f) := by simp
  _ = .comp (lmul' R) (.comp (Algebra.TensorProduct.map (HopfAlgebra.antipodeAlgHom R A)
       (.id R A)) <| .comp (Algebra.TensorProduct.map f f) (comulAlgHom R C)) := by
    rw [mul_def, Algebra.TensorProduct.map_comp]
    simp only [comp_assoc]
  _ = (HopfAlgebra.antipodeAlgHom R A * AlgHom.id R A).comp f := by
    simp only [mul_def, BialgHomClass.map_comp_comulAlgHom]
    simp only [comp_assoc]
  _ = _ := by simp [antipode_id_cancel, one_def, comp_assoc]

end AlgHom

open HopfAlgebra

namespace BialgHom
variable {B₁ B₂ : Type*} [CommSemiring A] [CommSemiring B₁] [CommSemiring B₂]
  [Algebra R B₁] [Algebra R B₂] [CommSemiring C]

section HopfAlgebra
variable [HopfAlgebra R A] [HopfAlgebra R C]

instance : Group (C →ₐ[R] B₁) where
  inv f := (f.comp <| HopfAlgebra.antipodeAlgHom R C)
  inv_mul_cancel l := by
    ext x
    dsimp [AlgHom.one_def, AlgHom.mul_def, ofId]
    trans l (algebraMap R C (counit x))
    · rw [← HopfAlgebra.mul_antipode_rTensor_comul_apply]
      induction comul (R := R) x with
      | zero => simp
      | add x y _ _ => simp [*]
      | tmul x y => simp
    · simp

lemma foo1 : Bialgebra.comulAlgHom R C =
    Algebra.TensorProduct.includeLeft *
    Algebra.TensorProduct.includeRight := by
  ext x
  simp only [comulAlgHom_apply, AlgHom.mul_def, AlgHom.coe_comp, Function.comp_apply]
  induction comul (R := R) x with
  | zero => simp
  | add x y hx hy => simp only [map_add, ← hx, ← hy]
  | tmul x y => simp

lemma foo2 : HopfAlgebra.antipodeAlgHom R C = (AlgHom.id _ _)⁻¹ := rfl

lemma comp_inv (f : C →ₐ[R] B₁) (g : B₁ →ₐ[R] B₂) : g.comp (f⁻¹) = (g.comp f)⁻¹ := rfl

lemma foobar : (Algebra.TensorProduct.map (HopfAlgebra.antipodeAlgHom R C)
    (HopfAlgebra.antipodeAlgHom R C)).comp
    ((Algebra.TensorProduct.comm R C C).toAlgHom.comp (Bialgebra.comulAlgHom R C)) =
      ((Bialgebra.comulAlgHom R C).comp ((HopfAlgebra.antipodeAlgHom R C))) := by
  simp [foo1, foo2, AlgHom.mul_distrib_comp, AlgHom.comp_mul_distrib, comp_inv]

variable [IsCocomm R A]

instance : Inv (C →ₐc[R] A) where inv f := (antipodeBialgHom R A).comp f

lemma inv_def (f : C →ₐc[R] A) : f⁻¹ = (antipodeBialgHom R A).comp f := rfl

@[simp] lemma inv_apply (f : C →ₐc[R] A) (c : C) : f⁻¹ c = antipode R (f c) := rfl

--private lemma inv_convMul_cancel (f : C →ₐc[R] A) : f⁻¹ * f = 1 := sorry

--instance : CommGroup (C →ₐc[R] A) where inv_mul_cancel := inv_convMul_cancel

end HopfAlgebra
end BialgHom
