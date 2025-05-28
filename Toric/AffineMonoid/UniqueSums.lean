/-
Copyright (c) 2025 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Algebra.FreeAbelianGroup.UniqueSums
import Toric.AffineMonoid.Embedding

/-!
# Affine monoids have unique sums
-/

variable {M : Type*}

instance AffineAddMonoid.to_twoUniqueSums [AddCancelCommMonoid M] [AddMonoid.FG M]
    [IsAddTorsionFree M] : TwoUniqueSums M :=
  .of_injective_addHom (embedding M).toAddHom embedding_injective inferInstance

@[to_additive existing AffineAddMonoid.to_twoUniqueSums]
instance AffineMonoid.to_twoUniqueProds [CancelCommMonoid M] [Monoid.FG M] [IsMulTorsionFree M] :
    TwoUniqueProds M :=
  Multiplicative.instTwoUniqueProdsOfTwoUniqueSums (M := Additive M)
