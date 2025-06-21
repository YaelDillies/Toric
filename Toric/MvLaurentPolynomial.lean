/-
Copyright (c) 2025 Patrick Luo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Patrick Luo, Paul Lezeau
-/
import Mathlib.GroupTheory.FreeAbelianGroup
import Mathlib.RingTheory.Bialgebra.MonoidAlgebra
import Mathlib.RingTheory.HopfAlgebra.Basic
import Toric.Mathlib.RingTheory.Bialgebra.Convolution

/-!
# Multivariate Laurent polynomials

This file defines Laurent polynomial rings over a base ring (or even semiring),
with variables from a general type `σ` (which could be infinite).
-/

open AddMonoidAlgebra

variable (σ R S : Type*)

abbrev MvLaurentPolynomial [Semiring R] := AddMonoidAlgebra R <| FreeAbelianGroup σ

noncomputable
def MonoidAlgebra.liftMulEquiv [CommRing R] [CommRing S] [Algebra R S] [CommMonoid σ] :
    (σ →* S) ≃* (MonoidAlgebra R σ →ₐ[R] S) where
  __ := MonoidAlgebra.lift R σ S
  map_mul' f g := by ext; simp

@[ext high]
lemma FreeGroup.ext_hom' {α G : Type*} [Monoid G] (f g : FreeGroup α →* G)
    (h : ∀ (a : α), f (of a) = g (of a)) : f = g := by
  ext x
  have (x) : f ((of x)⁻¹) = g ((of x)⁻¹) := by
    trans f ((of x)⁻¹) * f (of x) * g ((of x)⁻¹)
    · simp_rw [mul_assoc, h, ← _root_.map_mul, mul_inv_cancel, _root_.map_one, mul_one]
    · simp_rw [← _root_.map_mul, inv_mul_cancel, _root_.map_one, one_mul]
  induction x <;> simp [*, instMonad]

noncomputable
def MvLaurentPolynomial.liftEquiv [CommRing R] [CommRing S] [Algebra R S] :
    (σ → Sˣ) ≃* (MvLaurentPolynomial σ R →ₐ[R] S) := by
  refine .trans ?_ (MonoidAlgebra.liftMulEquiv ((Abelianization (FreeGroup σ))) _ _)
  refine
  { toFun f := (Units.coeHom S).comp (Abelianization.lift (FreeGroup.lift f))
    invFun f n := f.toHomUnits (.of (.of n))
    left_inv _ := by ext; simp
    right_inv f := by ext; simp
    map_mul' x y := by ext; simp }
