
/-
Copyright (c) 2025 Yaël Dillies, Michał Mrugała, Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Michał Mrugała, Andrew Yang
-/
import Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra
import Toric.Hopf.MonoidAlgebra
import Toric.Mathlib.Algebra.Category.CommHopfAlgCat

/-!
# The group algebra functor

We show that, for a domain `R`, `G ↦ R[G]` forms a fully faithful functor from commutative groups to
commutative `R`-Hopf algebras.
-/

open CategoryTheory Opposite

variable (R : Type*) [CommRing R]

/-- The functor of commutative monoid algebras. -/
@[simps obj map]
noncomputable def commMonAlg : CommMonCat ⥤ CommBialgCat R where
  obj M := .of R <| MonoidAlgebra R M
  map f := CommBialgCat.ofHom <| MonoidAlgebra.mapDomainBialgHom R f.hom

/-- The functor of commutative group algebras. -/
@[simps obj map]
noncomputable def commGrpAlg : CommGrp ⥤ CommHopfAlgCat R where
  obj G := .of R <| MonoidAlgebra R G
  map f := CommHopfAlgCat.ofHom <| MonoidAlgebra.mapDomainBialgHom R f.hom

variable {R} [IsDomain R]

/-- The group algebra functor over a domain is fully faithful. -/
noncomputable def commGrpAlg.fullyFaithful : (commGrpAlg R).FullyFaithful where
  preimage {X Y} f := CommGrp.ofHom <| MonoidAlgebra.mapDomainOfBialgHom f.hom

instance commGrpAlg.instFull : (commGrpAlg R).Full := fullyFaithful.full
instance commGrpAlg.instFaithful : (commGrpAlg R).Faithful := fullyFaithful.faithful
