
/-
Copyright (c) 2025 Yaël Dillies, Michał Mrugała, Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Michał Mrugała, Andrew Yang
-/
import Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra
import Toric.Hopf.HopfAlg
import Toric.Hopf.MonoidAlgebra
import Toric.Mathlib.CategoryTheory.Monoidal.Grp_

/-!
# The group algebra functor

We show that, for a field `k`, `G ↦ k[G]` forms a fully faithful functor from commutative groups to
commutative `k`-Hopf algebras.
-/

open CategoryTheory Opposite

section CommRing
variable (R : Type*) [CommRing R]

/-- The functor of commutative group algebras. -/
noncomputable def commGrpAlgebra : CommGrpᵒᵖ ⥤ Grp_ (CommAlg R)ᵒᵖ where
  obj G := .mk' <| op <| CommAlg.of R <| MonoidAlgebra R G.unop.carrier
  map f := Grp_.homMk (CommAlg.ofHom <| MonoidAlgebra.mapDomainBialgHom R f.unop.hom).op
  map_comp f g := by ext; simp

end CommRing

section Field
variable {k : Type*} [Field k]

/-- The group algebra functor over a field is fully faithful. -/
noncomputable def commGrpAlgebra.fullyFaithful : (commGrpAlgebra k).FullyFaithful where
  preimage {X Y} f :=
    .op <| CommGrp.ofHom <| MonoidAlgebra.mapDomainOfBialgHom (K := k) <|
      IsMon_Hom.toBialgHom (R := k) f.hom
  map_preimage {X Y} f := by simp [commGrpAlgebra]; rfl
  preimage_map {X Y} f := by simp [commGrpAlgebra]

instance commGrpAlgebra.instFull : (commGrpAlgebra k).Full := fullyFaithful.full
instance commGrpAlgebra.instFaithful : (commGrpAlgebra k).Faithful := fullyFaithful.faithful

end Field
