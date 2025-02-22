/-
Copyright (c) 2025 Yaël Dillies, Patrick Luo, Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Patrick Luo, Andrew Yang
-/
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.GroupTheory.FreeAbelianGroup
import Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra
import Toric.MvLaurentPolynomial

/-!
# The standard algebraic torus

This file defines the standard algebraic torus as `Spec ℂ[Fₙ]`.
-/

open AlgebraicGeometry CategoryTheory Limits HopfAlgebra Bialgebra Coalgebra CommRingCat

variable {R : CommRingCat} {n : ℕ} {X Y : Scheme}

variable (R n) in
/-- The standard algebraic torus over a ring `R`. `(Rˣ)ⁿ` as a scheme. -/
noncomputable abbrev Torus (n : ℕ) : Scheme := Spec <| .of <| MvLaurentPolynomial (Fin n) R

noncomputable instance : (Torus R n).Over (Spec R) where
  hom :=
    Spec.map <| CommRingCat.ofHom <| algebraMap R <| AddMonoidAlgebra R <| FreeAbelianGroup <| Fin n

/-- The algebraic action of the standard torus on itself. -/
noncomputable def torusMul : pullback.diagonalObj (Torus R n ↘ Spec R) ⟶ Torus R n :=
  (pullbackSpecIso _ _ _).hom ≫
  (Spec.map <| CommRingCat.ofHom <| comulAlgHom R <| MvLaurentPolynomial (Fin n) R)
