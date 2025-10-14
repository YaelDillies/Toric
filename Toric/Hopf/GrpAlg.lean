
/-
Copyright (c) 2025 Yaël Dillies, Michał Mrugała, Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Michał Mrugała, Andrew Yang
-/
import Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra
import Toric.Mathlib.Algebra.Category.CommHopfAlgCat
import Toric.Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra

/-!
# The group algebra functor

We show that, for a domain `R`, `G ↦ R[G]` forms a fully faithful functor from commutative groups to
commutative `R`-Hopf algebras.
-/

open CategoryTheory Opposite

variable {R : Type*} [CommRing R]

variable (R) in
/-- The functor of commutative monoid algebras. -/
@[simps obj map]
noncomputable def commMonAlg : CommMonCat ⥤ CommBialgCat R where
  obj M := .of R <| MonoidAlgebra R M
  map f := CommBialgCat.ofHom <| MonoidAlgebra.mapDomainBialgHom R f.hom

variable (R) in
/-- The functor of commutative group algebras. -/
@[simps obj map]
noncomputable def commGrpAlg : CommGrpCat ⥤ CommHopfAlgCat R where
  obj G := .of R <| MonoidAlgebra R G
  map f := CommHopfAlgCat.ofHom <| MonoidAlgebra.mapDomainBialgHom R f.hom

instance commMonAlg.instFaithful [Nontrivial R] : (commMonAlg R).Faithful where
  map_injective {G H} f g hfg := by
    ext a; simpa [Finsupp.single_left_inj one_ne_zero] using congr($hfg <| .single a 1)

instance commGrpAlg.instFaithful [Nontrivial R] : (commGrpAlg R).Faithful where
  map_injective {G H} f g hfg := by
    ext a; simpa [Finsupp.single_left_inj one_ne_zero] using congr($hfg <| .single a 1)

variable [IsDomain R]

/-- The group algebra functor over a domain is fully faithful. -/
noncomputable def commGrpAlg.fullyFaithful : (commGrpAlg R).FullyFaithful where
  preimage {X Y} f := CommGrpCat.ofHom <| MonoidAlgebra.mapDomainOfBialgHom f.hom

instance commGrpAlg.instFull : (commGrpAlg R).Full := fullyFaithful.full
