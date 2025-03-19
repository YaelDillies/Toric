/-
Copyright (c) 2025 Patrick Luo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Patrick Luo, Paul Lezeau
-/
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.GroupTheory.FreeAbelianGroup

/-!
# Multivariate Laurent polynomials

This file defines Laurent polynomial rings over a base ring (or even semiring),
with variables from a general type `σ` (which could be infinite).
-/

open AddMonoidAlgebra

variable (σ R : Type*)

abbrev MvLaurentPolynomial [Semiring R] := AddMonoidAlgebra R <| FreeAbelianGroup σ
