
/-
Copyright (c) 2025 Yaël Dillies, Michał Mrugała, Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Michał Mrugała, Andrew Yang
-/
import Toric.GroupScheme.HopfAffine
import Toric.Hopf.GrpAlg

/-!
# The spectrum of a group algebra functor

We show that, for a field `k`, `G ↦ Spec k[G]` forms a fully faithful functor from commutative
groups to group schemes over `Spec k`.
-/

open CategoryTheory Opposite AlgebraicGeometry

section CommRingCat
variable (R : CommRingCat)

/-- The diagonalizable monoid scheme functor. -/
noncomputable abbrev specCommMonAlg : CommMonCatᵒᵖ ⥤ Mon_ (Over (Spec R)) :=
  commMonAlg R ⋙ bialgSpec R

/-- The diagonalizable group scheme functor. -/
noncomputable abbrev specCommGrpAlg : CommGrpᵒᵖ ⥤ Grp_ (Over (Spec R)) :=
  commGrpAlg R ⋙ hopfSpec R

end CommRingCat

section Field
variable {k : Type*} [Field k]

/-- The diagonalizable group scheme functor over a field is fully faithful. -/
noncomputable
def specCommGrpAlg.fullyFaithful : (specCommGrpAlg (.of k)).FullyFaithful :=
  commGrpAlg.fullyFaithful.comp hopfSpec.fullyFaithful

instance specCommGrpAlg.instFull : (specCommGrpAlg <| .of k).Full := fullyFaithful.full
instance specCommGrpAlg.instFaithful : (specCommGrpAlg <| .of k).Faithful := fullyFaithful.faithful

end Field
