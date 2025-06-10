/-
Copyright (c) 2025 Michał Mrugała. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michał Mrugała
-/
import Mathlib.RingTheory.IsTensorProduct
import Toric.Mathlib.Algebra.MonoidAlgebra.Basic

/-!
In this file we show that monoid algebras are stable under pushout.
-/

noncomputable section

namespace MonoidAlgebra

open TensorProduct

variable {R σ S A B : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S] [CommMonoid σ]
variable [CommSemiring A] [Algebra R A] [CommSemiring B] [Algebra R B]

variable (R A B) in
/-- Tensoring `MonoidAlgebra R σ` on the left by an `R`-algebra `A` is algebraically
equivalent to `MonoidAlgebra A σ`. -/
noncomputable def tensorEquiv :
    A ⊗[R] MonoidAlgebra B σ ≃ₐ[A] MonoidAlgebra (A ⊗[R] B) σ :=
  AlgEquiv.ofAlgHom
    (Algebra.TensorProduct.lift
      ((IsScalarTower.toAlgHom A (A ⊗[R] B) _).comp Algebra.TensorProduct.includeLeft)
      (mapRangeAlgHom Algebra.TensorProduct.includeRight)
      (fun p n => .all _ _))
    (MonoidAlgebra.liftNCAlgHom (Algebra.TensorProduct.map (.id _ _) singleOneAlgHom)
        ((Algebra.TensorProduct.includeRight.toMonoidHom.comp (of B σ))) (fun _ _ ↦ .all _ _)) (by
      classical
      apply AlgHom.toLinearMap_injective
      ext
      simp [liftNCAlgHom, liftNCRingHom, single_one_mul_apply,
        single_apply, apply_ite ((1 : A) ⊗ₜ[R] ·)]) (by
      ext : 1
      · ext
      · apply AlgHom.toLinearMap_injective
        ext
        simp [liftNCAlgHom, liftNCRingHom, mapRangeAlgHom])

@[simp]
lemma tensorEquiv_tmul (a : A) (p : MonoidAlgebra B σ) :
    tensorEquiv R A B (a ⊗ₜ p) =
      a • mapRangeAlgHom (Algebra.TensorProduct.includeRight) p := by
  simp [tensorEquiv, Algebra.smul_def]

@[simp]
lemma algebraTensorAlgEquiv_symm_single (m : σ) (a : A) (b : B) :
    (tensorEquiv R A B).symm (single m (a ⊗ₜ b)) = a ⊗ₜ single m b := by
  simp [tensorEquiv]

/-- The tensor product of the monoid algebra by an algebra `N`
  is algebraically equivalent to a monoid algebra with
  coefficients in `N`. -/
noncomputable def scalarTensorEquiv :
    A ⊗[R] MonoidAlgebra R σ ≃ₐ[A] MonoidAlgebra A σ :=
  (tensorEquiv ..).trans (mapRangeAlgEquiv (Algebra.TensorProduct.rid R A A))

attribute [local instance] algebraMonoidAlgebra in
instance [Algebra S B] [Algebra A B] [Algebra R B] [IsScalarTower R A B] [IsScalarTower R S B]
    [Algebra.IsPushout R S A B] :
    Algebra.IsPushout R S (MonoidAlgebra A σ) (MonoidAlgebra B σ) where
  out := .of_equiv ((tensorEquiv (σ := σ) R S A).trans
      (mapRangeAlgEquiv (Algebra.IsPushout.equiv R S A B))).toLinearEquiv fun x ↦ by
    induction x using Finsupp.induction_linear
    · simp
    · simp_all
    · simp [mapRangeAlgHom, mapRangeRingHom, liftNCAlgHom, liftNCRingHom,
        Algebra.IsPushout.equiv_tmul]

attribute [local instance] algebraMonoidAlgebra in
instance [Algebra S B] [Algebra A B] [Algebra R B] [IsScalarTower R A B] [IsScalarTower R S B]
    [Algebra.IsPushout R A S B] : Algebra.IsPushout R (MonoidAlgebra A σ) S (MonoidAlgebra B σ) :=
  have : Algebra.IsPushout R S A B := .symm ‹_›
  .symm inferInstance

end MonoidAlgebra

end
