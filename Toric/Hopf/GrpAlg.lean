
/-
Copyright (c) 2025 Yaël Dillies, Michał Mrugała, Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Michał Mrugała, Andrew Yang
-/
import Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra
import Toric.Hopf.HopfAlg
import Toric.Hopf.MonoidAlgebra
import Toric.Mathlib.CategoryTheory.Monoidal.Cartesian.Grp_

/-!
# The group algebra functor

We show that, for a domain `R`, `G ↦ R[G]` forms a fully faithful functor from commutative groups to
commutative `R`-Hopf algebras.
-/

open CategoryTheory Opposite

variable (R : Type*) [CommRing R]

/-- The functor of commutative monoid algebras. -/
noncomputable def commMonAlg : CommMonCatᵒᵖ ⥤ Mon_ (CommAlg R)ᵒᵖ where
  obj M := .mk' <| op <| CommAlg.of R <| MonoidAlgebra R M.unop.carrier
  map f := .mk' (CommAlg.ofHom <| MonoidAlgebra.mapDomainBialgHom R f.unop.hom).op
  map_comp f g := by ext; simp

/-- The functor of commutative group algebras. -/
noncomputable def commGrpAlg : CommGrpᵒᵖ ⥤ Grp_ (CommAlg R)ᵒᵖ where
  obj G := .mk' <| op <| CommAlg.of R <| MonoidAlgebra R G.unop.carrier
  map f := Grp_.homMk (CommAlg.ofHom <| MonoidAlgebra.mapDomainBialgHom R f.unop.hom).op
  map_comp f g := by ext; simp

variable {R} [IsDomain R]

/-- The group algebra functor over a domain is fully faithful. -/
noncomputable def commGrpAlg.fullyFaithful : (commGrpAlg R).FullyFaithful where
  preimage {X Y} f :=
    .op <| CommGrp.ofHom <| MonoidAlgebra.mapDomainOfBialgHom (R := R) <|
      IsMon_Hom.toBialgHom (R := R) f.hom
  map_preimage {X Y} f := by simp [commGrpAlg]; rfl
  preimage_map {X Y} f := by simp [commGrpAlg]

instance commGrpAlg.instFull : (commGrpAlg R).Full := fullyFaithful.full
instance commGrpAlg.instFaithful : (commGrpAlg R).Faithful := fullyFaithful.faithful
