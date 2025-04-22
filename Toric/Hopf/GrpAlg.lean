
/-
Copyright (c) 2025 Yaël Dillies, Michał Mrugała, Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Michał Mrugała, Andrew Yang
-/
import Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra
import Mathlib.Tactic.Algebraize
import Toric.Mathlib.Algebra.MonoidAlgebra.Basic
import Toric.Hopf.HopfAlg
import Toric.Hopf.MonoidAlgebra
import Toric.Mathlib.CategoryTheory.Monoidal.Grp_

/-!
# The group algebra functor

We show that, for a field `k`, `G ↦ k[G]` forms a fully faithful functor from commutative groups to
commutative `k`-Hopf algebras.
-/

open CategoryTheory Opposite TensorProduct

universe u

section CommRing
variable {R R' : Type u} [CommRing R] [CommRing R'] (u : R →+* R')

variable (R) in
/-- The functor of commutative group algebras. -/
noncomputable def commGrpAlgebra : CommGrpᵒᵖ ⥤ Grp_ (CommAlg R)ᵒᵖ where
  obj G := .mk' <| op <| CommAlg.of R <| MonoidAlgebra R G.unop.carrier
  map f := Grp_.homMk (CommAlg.ofHom <| MonoidAlgebra.mapDomainBialgHom R f.unop.hom).op
  map_comp f g := by ext; simp

-- For some reason I get an error when `R` and `R'` are in different universes.
noncomputable def commGrpAlgebra_baseChange :
    commGrpAlgebra R' ≅ commGrpAlgebra R ⋙ (commAlgBaseChange u).op.mapGrp := by
  algebraize [u]
  refine NatIso.ofComponents (fun A ↦ Grp_.mkIso (AlgEquiv.toCommAlgIso
    (MonoidAlgebra.baseChangeAlgEquiv R R' (unop A).1).symm).op ?_ ?_) ?_
  · apply Quiver.Hom.unop_inj
    ext x
    set y : R' ⊗[R] MonoidAlgebra R (unop A).1 := x
    dsimp
    erw [MonoidAlgebra.baseChangeAlgEquiv_symm_counit y]
    sorry
  · sorry
  · sorry

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
