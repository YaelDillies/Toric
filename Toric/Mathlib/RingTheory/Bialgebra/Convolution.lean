/-
Copyright (c) 2025 Yaël Dillies, Michał Mrugała, Yunzhou Xie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Michał Mrugała, Yunzhou Xie
-/
import Mathlib.RingTheory.Bialgebra.TensorProduct
import Toric.Mathlib.RingTheory.Bialgebra.Hom
import Toric.Mathlib.RingTheory.Coalgebra.Convolution

/-!
# Convolution product on bialgebra homs

This file constructs the ring structure on algebra homs `C → A` where `C` is a bialgebra and `A` an
algebra, and also the ring structure on bialgebra homs `C → A` where `C` and `A` are bialgebras.
Both multiplications are given by
```
         .
        / \
f * g = f g
        \ /
         .
```
-/

suppress_compilation

open Coalgebra Bialgebra TensorProduct

-- TODO: Remove universe monomorphism
-- TODO: Generalise to semirings
universe u
variable {R A B C : Type u} [CommRing R]

namespace AlgHom
variable [CommSemiring A] [CommSemiring B] [Semiring C] [Bialgebra R C] [Algebra R A]

instance : One (C →ₐ[R] A) where one := (Algebra.ofId R A).comp <| counitAlgHom R C
instance : Mul (C →ₐ[R] A) where
  mul f g := .comp (mulAlgHom R A) <| .comp (Algebra.TensorProduct.map f g) <| comulAlgHom R C

instance : Pow (C →ₐ[R] A) ℕ := ⟨fun f n ↦ npowRec n f⟩

lemma one_def : (1 : C →ₐ[R] A) = (Algebra.ofId R A).comp (counitAlgHom ..) := rfl
lemma mul_def (f g : C →ₐ[R] A) : f * g =
    (.comp (mulAlgHom R A) <| .comp (Algebra.TensorProduct.map f g) <| comulAlgHom R C) := rfl

lemma pow_succ (f : C →ₐ[R] A) (n : ℕ) : f ^ (n + 1) = (f ^ n) * f := rfl

@[simp] lemma one_apply' (c : C) : (1 : C →ₐ[R] A) c = algebraMap R A (counit c) := rfl

lemma toLinearMap_one : (1 : C →ₐ[R] A) = (1 : C →ₗ[R] A) := rfl
lemma toLinearMap_mul (f g : C →ₐ[R] A) : (f * g).toLinearMap = f.toLinearMap * g.toLinearMap := rfl
lemma toLinearMap_pow (f : C →ₐ[R] A) (n : ℕ) : (f ^ n).toLinearMap = f.toLinearMap ^ n := by
  induction' n with n hn
  · rfl
  · simp only [pow_succ, toLinearMap_mul, hn, _root_.pow_succ]

instance : CommMonoid (C →ₐ[R] A) :=
  toLinearMap_injective.commMonoid _ toLinearMap_one toLinearMap_mul toLinearMap_pow

lemma mul_distrib_comp [Bialgebra R B] (f g : C →ₐ A) (h : B →ₐc[R] C) :
    AlgHom.comp (f * g) (h : B →ₐ[R] C) = (.comp f h) * (.comp g h) := calc
  _ = (.comp (mulAlgHom R A) <| .comp (Algebra.TensorProduct.map f g) <|
      .comp (Algebra.TensorProduct.map (h : B →ₐ[R] C) (h : B →ₐ[R] C)) (comulAlgHom R B)) := by
    simp [mul_def, comp_assoc]
  _ = (.comp (mulAlgHom R A) <|
      .comp (Algebra.TensorProduct.map (.comp f h) (.comp g h)) (comulAlgHom R B)) := by
    rw [Algebra.TensorProduct.map_comp]
    simp [comp_assoc]
  _ = _ := by simp [mul_def]

lemma comp_mul_distrib [Algebra R B] (f g : C →ₐ[R] A) (h : A →ₐ[R] B) :
    h.comp (f * g) = h.comp f * h.comp g := by
  apply toLinearMap_injective
  simp [toLinearMap_mul, LinearMap.comp_mul_distrib]

end AlgHom

namespace BialgHom
variable [CommRing A] [CommRing C] [Bialgebra R A] [Bialgebra R C]

instance : One (C →ₐc[R] A) where one := (unitBialgHom R A).comp <| counitBialgHom R C

lemma one_def : (1 : C →ₐc[R] A) = (unitBialgHom R A).comp (counitBialgHom ..) := rfl

@[simp] lemma one_apply' (c : C) : (1 : C →ₐc[R] A) c = algebraMap R A (counit c) := rfl

lemma toLinearMap_one : (1 : C →ₐc[R] A).toLinearMap = (1 : C →ₗ[R] A) := rfl

variable [IsCocomm R C]

instance : Mul (C →ₐc[R] A) where
  mul f g := .comp (mulBialgHom R A) <| .comp (Bialgebra.TensorProduct.map f g) <| comulBialgHom R C

instance : Pow (C →ₐc[R] A) ℕ := ⟨fun f n ↦ npowRec n f⟩

lemma mul_def (f g : C →ₐc[R] A) : f * g =
    (.comp (mulBialgHom R A) <| .comp (Bialgebra.TensorProduct.map f g) <| comulBialgHom R C) := rfl

lemma pow_succ (f : C →ₐc[R] A) (n : ℕ) : f ^ (n + 1) = (f ^ n) * f := rfl

-- @[simp]
-- lemma mul_apply'' (f g : C →ₐc[R] A) (c : C) : (f * g) c = mul' R A (.map f g (comul c)) := rfl

lemma toLinearMap_mul (f g : C →ₐc[R] A) : (f * g).toLinearMap = f.toLinearMap * g.toLinearMap :=
  rfl

lemma toLinearMap_pow (f : C →ₐc[R] A) (n : ℕ) : (f ^ n).toLinearMap = f.toLinearMap ^ n := by
  induction' n with n hn
  · rfl
  · rw [pow_succ, _root_.pow_succ, toLinearMap_mul, hn]

instance : CommMonoid (C →ₐc[R] A) :=
  coe_linearMap_injective.commMonoid _ toLinearMap_one toLinearMap_mul toLinearMap_pow

end BialgHom
