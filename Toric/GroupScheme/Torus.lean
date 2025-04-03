/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.Algebra.Category.Grp.Adjunctions
import Mathlib.Algebra.Category.Ring.Adjunctions
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.CategoryTheory.Adjunction.Opposites
import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
import Toric.Mathlib.Algebra.Category.Grp.Basic
import Toric.Mathlib.Algebra.Category.MonCat.Basic
import Toric.Mathlib.CategoryTheory.Comma.Over.Pullback
import Toric.Mathlib.CategoryTheory.Monoidal.CommGrp_
import Toric.Mathlib.CategoryTheory.Yoneda
import Toric.MvLaurentPolynomial

/-!
# The standard algebraic torus

This file defines the standard algebraic torus over `Spec R` as `Spec (R ⊗ ℤ[Fₙ])`.
-/

noncomputable section

open CategoryTheory Opposite Limits

namespace AlgebraicGeometry.Scheme

attribute [local instance] ChosenFiniteProducts.ofFiniteProducts

def DiagInt (M : Type*) [CommMonoid M] : Scheme := Spec (.of (MonoidAlgebra (ULift ℤ) M))

def DiagInt.representableBy (M : Type*) [CommMonoid M] :
    (Scheme.Γ ⋙ forget₂ _ CommMonCat ⋙
      CommMonCat.coyoneda.obj (op (.of M)) ⋙ forget _).RepresentableBy
      (DiagInt M) :=
  letI e : opOp CommMonCat ⋙ yoneda.obj (op (.of M)) ≅ CommMonCat.coyoneda.obj _ ⋙ forget _ :=
    opOpYoneda.app (op _) ≪≫ CommMonCat.coyonedaForget.symm.app (op (.of M))
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
    CommGrp.forget₂CommMonAdj.op.comp <| AddCommGrp.equivalence.toAdjunction.op.comp <|
    (AddCommGrp.adj.op)).representableBy (op σ)).ofIso
    (isoWhiskerLeft (Scheme.Γ ⋙ forget₂ _ CommMonCat ⋙ CommMonCat.units ⋙ forget CommGrp)
      (opOpYoneda.app _))

instance (σ : Type*) : CommGrp_Class (TorusInt σ) :=
  .ofRepresentableBy _
    (Scheme.Γ ⋙ forget₂ _ CommMonCat ⋙ CommMonCat.units ⋙ CommGrp.coyonedaRight.obj (op σ))
      (TorusInt.representableBy σ)

def CommGrp_Torus (S : Scheme) (σ : Type*) : CommGrp_ (Over S) :=
  ((Over.equivalenceOfIsTerminal terminalIsTerminal).inverse ⋙
    Over.pullback (terminal.from _)).mapCommGrp.obj
      (.mk' (TorusInt σ))

/-- The (split) algebraic torus over `S` indexed by `σ`. -/
def SplitTorus (S : Scheme) (σ : Type*) : Scheme := (CommGrp_Torus S σ).X.left

notation "𝔾ₘ["S"]" => SplitTorus S PUnit

example (S : Scheme) (σ : Type*) :
    SplitTorus S σ = pullback (terminal.from (TorusInt σ)) (terminal.from S) := rfl

instance SplitTorus.instCanonicallyOver (S : Scheme) (σ : Type*) :
    (SplitTorus S σ).CanonicallyOver S where
  hom := (CommGrp_Torus S σ).X.hom

instance (S : Scheme) (σ : Type*) : CommGrp_Class (Over.mk (SplitTorus S σ ↘ S)) :=
  inferInstanceAs (CommGrp_Class (CommGrp_Torus S σ).X)

def SplitTorus.representableBy (S : Scheme) (σ : Type*) :
    ((Over.forget _).op ⋙ Scheme.Γ ⋙ forget₂ _ CommMonCat ⋙ CommMonCat.units ⋙
      CommGrp.coyonedaRight.obj (op σ) ⋙ forget _).RepresentableBy
      (Over.mk (SplitTorus S σ ↘ S)) :=
  ((((Over.mapPullbackAdj (terminal.from S)).comp
    (Over.equivalenceOfIsTerminal terminalIsTerminal).toAdjunction).comp <|
    (ΓSpec.adjunction.comp <| (CommRingCat.forget₂Adj CommRingCat.isInitial).op.comp <|
      CommGrp.forget₂CommMonAdj.op.comp <| AddCommGrp.equivalence.toAdjunction.op.comp <|
    (AddCommGrp.adj.op))).representableBy (op σ)).ofIso
    (isoWhiskerRight (NatIso.op (Over.forgetMapTerminal S))
      (Scheme.Γ ⋙ forget₂ _ CommMonCat ⋙
        CommMonCat.units ⋙ forget _ ⋙ opOp _ ⋙ yoneda.obj (op σ)) ≪≫
        (isoWhiskerLeft ((Over.forget _).op ⋙ Scheme.Γ ⋙ forget₂ _ CommMonCat ⋙
          CommMonCat.units ⋙ forget CommGrp) (opOpYoneda.app _)))

/-- The split torus of dimension `n` over `Spec R`. -/
notation "𝔾ₘ[" R ", " n "]" => Over.mk (SplitTorus (Spec R) (ULift <| Fin n) ↘ Spec R)

/-- The split torus with dimensions `σ` over `Spec R` is isomorphic to `Spec R[ℤ^σ]`. -/
def splitTorusIsoSpec (R : CommRingCat) (σ : Type*) :
    SplitTorus (Spec R) σ ≅ Spec (.of <| MvLaurentPolynomial σ R) := sorry

/-- The split torus of dimension `n` over `Spec R` is isomorphic to `Spec R[ℤⁿ]`. -/
def splitTorusIsoSpecOver (R : CommRingCat) (n : ℕ) :
    𝔾ₘ[R, n] ≅
      .mk <| Spec.map <| CommRingCat.ofHom <| algebraMap R (MvLaurentPolynomial (Fin n) R) :=
  Over.isoMk
    ((splitTorusIsoSpec _ _).trans <| Scheme.Spec.mapIso <| .op <| RingEquiv.toCommRingCatIso <|
      (AddMonoidAlgebra.domCongr R _ <| FreeAbelianGroup.equivOfEquiv Equiv.ulift.symm).toRingEquiv)
    sorry

end AlgebraicGeometry.Scheme
