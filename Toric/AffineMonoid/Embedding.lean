/-
Copyright (c) 2025 Yaël Dillies, Patrick Luo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Patrick Luo
-/
import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.Algebra.FreeAbelianGroup.UniqueSums
import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors
import Mathlib.GroupTheory.MonoidLocalization.GrothendieckGroup
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.FreeModule.PID
import Toric.Mathlib.Algebra.NoZeroSMulDivisors.Defs
import Toric.Mathlib.GroupTheory.MonoidLocalization.Basic

/-!
# Affine monoids embed into `ℤⁿ`

This file proves that cancellative finitely generated torsion-free monoids (aka *affine monoids* or
*affine semigroups*) embed into `ℤⁿ`.

## TODO

Does this generalise to modules over rings other than `ℤ`? Probably.
-/

open Algebra AddLocalization AddMonoidAlgebra Function

variable {M : Type*} [AddCancelCommMonoid M] [AddMonoid.FG M] [IsAddTorsionFree M]

namespace AffineMonoid

variable (M) in
/-- The dimension of an affine monoid `M`, namely the minimum `n` for which `M` embeds into `ℤⁿ`. -/
noncomputable abbrev dim := Module.finrank ℤ <| GrothendieckAddGroup M

variable (M) in
/-- An embedding of `M` into `ℤ ^ dim M`. -/
noncomputable def embedding : M →+ FreeAbelianGroup (Fin (dim M)) :=
  .comp (FreeAbelianGroup.equivFinsupp _).symm.toAddMonoidHom <|
  .comp (Module.finBasis ℤ _).repr.toAddMonoidHom
    (addMonoidOf ⊤).toAddMonoidHom

lemma embedding_injective : Injective (embedding M) := by
  simpa [embedding] using mk_left_injective 0

end AffineMonoid

open AffineMonoid

variable {R : Type*} [CommRing R]

instance AddMonoidAlgebra.instNoZeroDivisorsOfFG [NoZeroDivisors R] :
    NoZeroDivisors (AddMonoidAlgebra R M) :=
  (mapDomain_injective embedding_injective).noZeroDivisors (mapDomainRingHom R <| embedding M)
    (map_zero _) (map_mul _)

instance AddMonoidAlgebra.instIsDomainOfFG [IsDomain R] : IsDomain (AddMonoidAlgebra R M) :=
  (mapDomain_injective embedding_injective).isDomain <| mapDomainRingHom R <| embedding M
