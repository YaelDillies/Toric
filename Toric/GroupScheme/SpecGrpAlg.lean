
/-
Copyright (c) 2025 Yaël Dillies, Michał Mrugała, Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Michał Mrugała, Andrew Yang
-/
import Toric.GroupScheme.HopfAffine
import Toric.GroupScheme.SchemeOver
import Toric.Hopf.GrpAlg

/-!
# The spectrum of a group algebra functor

We show that, for a field `k`, `G ↦ Spec k[G]` forms a fully faithful functor from commutative
groups to group schemes over `Spec k`.
-/

open CategoryTheory Opposite AlgebraicGeometry

section CommRingCat
variable (R : CommRingCat)

/-- The diagonalizable group scheme functor. -/
noncomputable abbrev specCommGrpAlgebra : CommGrpᵒᵖ ⥤ Grp_ (Over (Spec R)) :=
  commGrpAlgebra R ⋙ hopfSpec R

end CommRingCat

section Field
variable {k : Type*} [Field k]

/-- The diagonalizable group scheme functor over a field is fully faithful. -/
noncomputable
def specCommGrpAlgebra.fullyFaithful : (specCommGrpAlgebra (.of k)).FullyFaithful :=
  commGrpAlgebra.fullyFaithful.comp hopfSpec.fullyFaithful

instance specCommGrpAlgebra.instFull : (specCommGrpAlgebra <| .of k).Full := fullyFaithful.full
instance specCommGrpAlgebra.instFaithful : (specCommGrpAlgebra <| .of k).Faithful :=
  fullyFaithful.faithful

end Field
