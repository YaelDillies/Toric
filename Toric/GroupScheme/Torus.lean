/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.Algebra.Category.Grp.Adjunctions
import Mathlib.Algebra.Category.Grp.EquivalenceGroupAddGroup
import Mathlib.Algebra.Category.Ring.Adjunctions
import Mathlib.AlgebraicGeometry.Limits
import Toric.GroupScheme.HopfAffine
import Toric.Mathlib.Algebra.Category.Grp.Basic
import Toric.Mathlib.Algebra.Category.MonCat.Basic
import Toric.Mathlib.CategoryTheory.Monoidal.Cartesian.CommGrp_
import Toric.MvLaurentPolynomial

/-!
# The standard algebraic torus

This file defines the standard algebraic torus over `Spec R` as `Spec (R ⊗ ℤ[Fₙ])`.
-/

noncomputable section

open CategoryTheory Opposite Limits

namespace AlgebraicGeometry.Scheme

def DiagInt (M : Type*) [CommMonoid M] : Scheme := Spec (.of (MonoidAlgebra (ULift ℤ) M))

def DiagInt.representableBy (M : Type*) [CommMonoid M] :
    (Scheme.Γ ⋙ forget₂ _ CommMonCat ⋙
      CommMonCat.coyoneda.obj (op (.of M)) ⋙ forget _).RepresentableBy
      (DiagInt M) :=
  letI e : opOp CommMonCat ⋙ yoneda.obj (op (.of M)) ≅ CommMonCat.coyoneda.obj _ ⋙ forget _ :=
    Coyoneda.opIso.app (op _) ≪≫ CommMonCat.coyonedaForget.symm.app (op (.of M))
  letI e' := isoWhiskerLeft (Scheme.Γ ⋙ forget₂ _ CommMonCat) e
  ((ΓSpec.adjunction.comp (CommRingCat.forget₂Adj CommRingCat.isInitial).op).representableBy
    (op (.of M))).ofIso e'

instance (M : Type*) [CommMonoid M] : Mon_Class (DiagInt M) :=
  Mon_Class.ofRepresentableBy _ (Scheme.Γ ⋙ forget₂ _ CommMonCat ⋙
    CommMonCat.coyoneda.obj (op (.of M)) ⋙ forget₂ _ _) (DiagInt.representableBy M)

def TorusInt (σ : Type*) : Scheme := DiagInt (Multiplicative (FreeAbelianGroup σ))

def TorusInt.representableBy (σ : Type*) :
    (Scheme.Γ ⋙ forget₂ _ CommMonCat ⋙ CommMonCat.units ⋙
      CommGrp.coyonedaRight.obj (op σ) ⋙ forget _).RepresentableBy
        (TorusInt σ) :=
  ((ΓSpec.adjunction.comp <| (CommRingCat.forget₂Adj CommRingCat.isInitial).op.comp <|
    CommGrp.forget₂CommMonAdj.op.comp <|
      commGroupAddCommGroupEquivalence.symm.toAdjunction.op.comp <|
        AddCommGrp.adj.op).representableBy (op σ)).ofIso <|
    isoWhiskerLeft (Scheme.Γ ⋙ forget₂ _ CommMonCat ⋙ CommMonCat.units ⋙ forget CommGrp)
      (Coyoneda.opIso.app _)

instance (σ : Type*) : CommGrp_Class (TorusInt σ) :=
  .ofRepresentableBy _
    (Scheme.Γ ⋙ forget₂ _ CommMonCat ⋙ CommMonCat.units ⋙ CommGrp.coyonedaRight.obj (op σ))
      (TorusInt.representableBy σ)

attribute [local instance] Functor.Braided.ofChosenFiniteProducts in
def CommGrp_Torus (S : Scheme) (σ : Type*) : CommGrp_ (Over S) :=
  ((Over.equivalenceOfIsTerminal terminalIsTerminal).inverse ⋙
    Over.pullback (terminal.from _)).mapCommGrp.obj
      (.mk' (TorusInt σ))

/-- The (split) algebraic torus over `S` indexed by `σ`. -/
def splitTorus (S : Scheme) (σ : Type*) : Scheme := (CommGrp_Torus S σ).X.left

@[inherit_doc splitTorus]
notation3 "𝔾ₘ[" S ", " σ "]" => splitTorus S σ

/-- The (split) algebraic circle over `S`. -/
notation3 "𝔾ₘ["S"]" => splitTorus S PUnit

/-- The split torus over a general base is defined by base-changing the torus over `ℤ`. -/
example (S : Scheme) (σ : Type*) :
    splitTorus S σ = pullback (terminal.from (TorusInt σ)) (terminal.from S) := rfl

instance splitTorus.instCanonicallyOver (S : Scheme) (σ : Type*) :
    (splitTorus S σ).CanonicallyOver S where
  hom := (CommGrp_Torus S σ).X.hom

instance (S : Scheme) (σ : Type*) : CommGrp_Class (asOver (splitTorus S σ) S) :=
  inferInstanceAs (CommGrp_Class (CommGrp_Torus S σ).X)

def splitTorus.representableBy (S : Scheme) (σ : Type*) :
    ((Over.forget _).op ⋙ Scheme.Γ ⋙ forget₂ _ CommMonCat ⋙ CommMonCat.units ⋙
      CommGrp.coyonedaRight.obj (op σ) ⋙ forget _).RepresentableBy
      (Over.mk (splitTorus S σ ↘ S)) :=
  ((((Over.mapPullbackAdj (terminal.from S)).comp
    (Over.equivalenceOfIsTerminal terminalIsTerminal).toAdjunction).comp <|
    (ΓSpec.adjunction.comp <| (CommRingCat.forget₂Adj CommRingCat.isInitial).op.comp <|
      CommGrp.forget₂CommMonAdj.op.comp <|
        commGroupAddCommGroupEquivalence.symm.toAdjunction.op.comp <|
          AddCommGrp.adj.op)).representableBy (op σ)).ofIso <|
    isoWhiskerRight (NatIso.op (Over.forgetMapTerminal _ _))
      (Scheme.Γ ⋙ forget₂ _ CommMonCat ⋙
        CommMonCat.units ⋙ forget _ ⋙ opOp _ ⋙ yoneda.obj (op σ)) ≪≫
        (isoWhiskerLeft ((Over.forget _).op ⋙ Scheme.Γ ⋙ forget₂ _ CommMonCat ⋙
          CommMonCat.units ⋙ forget CommGrp) (Coyoneda.opIso.app _))

/-- The split torus with dimensions `σ` over `Spec R` is isomorphic to `Spec R[ℤ^σ]`. -/
def splitTorusIsoSpec (R : CommRingCat) (σ : Type*) :
    splitTorus (Spec R) σ ≅ Spec (.of <| MvLaurentPolynomial σ R) := sorry

/-- The split torus with dimensions `σ` over `Spec R` is isomorphic to `Spec R[ℤ^σ]`. -/
def splitTorusIsoSpecOver (R : Type _) [CommRing R] (σ : Type*) :
    asOver 𝔾ₘ[Spec (.of R), σ] (Spec (.of R)) ≅
      asOver (Spec <| .of <| MvLaurentPolynomial σ R) (Spec (.of R)) :=
  Over.isoMk (splitTorusIsoSpec _ _) sorry

end AlgebraicGeometry.Scheme
