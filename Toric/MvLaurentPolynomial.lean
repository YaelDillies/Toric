/-
Copyright (c) 2025 Patrick Luo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Patrick Luo, Paul Lezeau
-/
import Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors
import Toric.Mathlib.Algebra.Group.UniqueProds.Basic
import Toric.Mathlib.Algebra.MonoidAlgebra.Defs

/-!
# Multivariate Laurent polynomials

This file defines Laurent polynomial rings over a base ring (or even semiring),
with variables from a general type `σ` (which could be infinite).
-/

open AddMonoidAlgebra

variable (σ : Type*) (R : Type*)

abbrev MvLaurentPolynomial [Semiring R] := AddMonoidAlgebra R <| FreeAbelianGroup σ

namespace MvLaurentPolynomial

section Semiring

variable [Semiring R] [Nontrivial R] [Nonempty σ]

instance : Nontrivial (MvLaurentPolynomial σ R) where
  exists_pair_ne := by
    use 0, AddMonoidAlgebra.single (FreeAbelianGroup.of Classical.ofNonempty) 1
    exact (AddMonoidAlgebra.single_ne_zero.mpr (zero_ne_one' R).symm).symm

end Semiring

variable [Ring R] [IsDomain R] [NoZeroDivisors R]

instance instIsDomain : IsDomain (MvLaurentPolynomial σ R) :=
  NoZeroDivisors.to_isDomain (MvLaurentPolynomial σ R)

end MvLaurentPolynomial


#min_imports
