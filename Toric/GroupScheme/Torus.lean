/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Toric.GroupScheme.Diagonalizable
import Toric.MvLaurentPolynomial

/-!
# The standard algebraic torus

This file defines the standard algebraic torus over `Spec R` as `Spec (R ⊗ ℤ[Fₙ])`.
-/

noncomputable section

open CategoryTheory Opposite Limits

namespace AlgebraicGeometry.Scheme

universe u v

/-- The (split) algebraic torus over `S` indexed by `σ`. -/
abbrev Torus (S : Scheme.{max u v}) (σ : Type v) : Scheme.{max u v} :=
  Diag S <| Multiplicative <| ULift.{v} <| FreeAbelianGroup σ

@[inherit_doc Torus]
notation3 "𝔾ₘ[" S ", " σ "]" => Torus S σ

/-- The (split) algebraic circle over `S`. -/
notation3 "𝔾ₘ["S"]" => Torus S Unit

-- def torus.representableBy (S : Scheme) (σ : Type*) :
--     ((Over.forget _).op ⋙ Scheme.Γ ⋙ forget₂ _ CommMonCat ⋙ CommMonCat.units ⋙
--       CommGrp.coyonedaRight.obj (op σ) ⋙ forget _).RepresentableBy
--       (asOver 𝔾ₘ[S, σ] S) :=
--   ((((Over.mapPullbackAdj (terminal.from S)).comp
--     (Over.equivalenceOfIsTerminal terminalIsTerminal).toAdjunction).comp <|
--     (ΓSpec.adjunction.comp <| (CommRingCat.forget₂Adj CommRingCat.isInitial).op.comp <|
--       CommGrp.forget₂CommMonAdj.op.comp <|
--         commGroupAddCommGroupEquivalence.symm.toAdjunction.op.comp <|
--           AddCommGrp.adj.op)).representableBy (op σ)).ofIso <|
--     isoWhiskerRight (NatIso.op (Over.forgetMapTerminal _ _))
--       (Scheme.Γ ⋙ forget₂ _ CommMonCat ⋙
--         CommMonCat.units ⋙ forget _ ⋙ opOp _ ⋙ yoneda.obj (op σ)) ≪≫
--         (isoWhiskerLeft ((Over.forget _).op ⋙ Scheme.Γ ⋙ forget₂ _ CommMonCat ⋙
--           CommMonCat.units ⋙ forget CommGrp) (Coyoneda.opIso.app _))

/-- The split torus with dimensions `σ` over `Spec R` is isomorphic to `Spec R[ℤ^σ]`. -/
def torusIsoSpec (R : CommRingCat) (σ : Type*) :
    𝔾ₘ[Spec R, σ] ≅ Spec (.of <| MvLaurentPolynomial σ R) := sorry

/-- The split torus with dimensions `σ` over `Spec R` is isomorphic to `Spec R[ℤ^σ]`. -/
def torusIsoSpecOver (R : CommRingCat) (σ : Type*) :
    asOver 𝔾ₘ[Spec R, σ] (Spec R) ≅ asOver (Spec <| .of <| MvLaurentPolynomial σ R) (Spec R) :=
  Over.isoMk (torusIsoSpec _ _) sorry

end AlgebraicGeometry.Scheme
