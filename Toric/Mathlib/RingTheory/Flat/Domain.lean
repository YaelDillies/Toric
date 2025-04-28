/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RingTheory.Flat.Localization

/-!
# Flat modules in domains

We show that the tensor product of two injective linear maps is injective if the sources are flat
and the ring is an integral domain.
-/

universe u

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
variable [AddCommGroup N] [Module R N]
variable {P Q : Type*} [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q]

open TensorProduct Function

attribute [local instance 1100] Module.Free.of_divisionRing Module.Flat.of_free in
/-- Tensor product of injective maps over domains are injective under some flatness conditions.
Also see `TensorProduct.map_injective_of_flat_flat`
for different flatness conditions but without the domain assumption. -/
lemma TensorProduct.map_injective_of_flat_flat_of_isDomain [IsDomain R]
    (f : P →ₗ[R] M) (g : Q →ₗ[R] N) [H : Module.Flat R P] [Module.Flat R Q]
    (hf : Injective f) (hg : Injective g) : Injective (TensorProduct.map f g) := sorry

/-- Tensor product of linearly independent families is linearly independent over domains.
This is true over non-domains if one of the modules is flat.
See `LinearIndependent.tmul_of_flat_left`. -/
lemma LinearIndependent.tmul_of_isDomain [IsDomain R]
    {ι ι' : Type*} {v : ι → M} (hv : LinearIndependent R v)
    {w : ι' → N} (hw : LinearIndependent R w) :
    LinearIndependent R fun i : ι × ι' ↦ v i.1 ⊗ₜ[R] w i.2 := by
  rw [LinearIndependent]
  convert (TensorProduct.map_injective_of_flat_flat_of_isDomain _ _ hv hw).comp
    (finsuppTensorFinsupp' _ _ _).symm.injective
  rw [← LinearEquiv.coe_toLinearMap, ← LinearMap.coe_comp]
  congr!
  ext i
  simp [finsuppTensorFinsupp'_symm_single_eq_single_one_tmul]
