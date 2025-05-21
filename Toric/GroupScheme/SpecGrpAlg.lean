
/-
Copyright (c) 2025 Yaël Dillies, Michał Mrugała, Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Michał Mrugała, Andrew Yang
-/
import Toric.GroupScheme.HopfAffine
import Toric.Hopf.GrpAlg

/-!
# The spectrum of a group algebra functor

We show that, for a domain `R`, `G ↦ Spec R[G]` forms a fully faithful functor from commutative
groups to group schemes over `Spec R`.
-/

open CategoryTheory Opposite AlgebraicGeometry

universe u
variable (R : CommRingCat.{u})

/-- The diagonalizable monoid scheme functor. -/
noncomputable abbrev specCommMonAlg : CommMonCat.{u}ᵒᵖ ⥤ Mon_ (Over (Spec R)) :=
  (commMonAlg R).op ⋙ bialgSpec R

/-- The diagonalizable group scheme functor. -/
noncomputable abbrev specCommGrpAlg : CommGrp.{u}ᵒᵖ ⥤ Grp_ (Over (Spec R)) :=
  (commGrpAlg R).op ⋙ hopfSpec R

variable {R} [IsDomain R]

/-- The diagonalizable group scheme functor over a domain is fully faithful. -/
noncomputable
def specCommGrpAlg.fullyFaithful : (specCommGrpAlg (.of R)).FullyFaithful :=
  commGrpAlg.fullyFaithful.op.comp hopfSpec.fullyFaithful

instance specCommGrpAlg.instFull : (specCommGrpAlg <| .of R).Full := fullyFaithful.full
instance specCommGrpAlg.instFaithful : (specCommGrpAlg <| .of R).Faithful := fullyFaithful.faithful
