/-
Copyright (c) 2025 Yaël Dillies, Michał Mrugała. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Michał Mrugała
-/
import Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra
import Toric.GroupScheme.Torus
import Toric.Mathlib.Algebra.Group.Equiv.Basic
import Toric.Mathlib.RingTheory.Coalgebra.MonoidAlgebra

/-!
# The lattices of characters and cocharacters
-/

open AddMonoidAlgebra CategoryTheory

namespace AlgebraicGeometry.Scheme
universe u

section general_base
variable {σ : Type u} {S G : Scheme.{u}} [G.Over S]

section Grp_Class
variable [Grp_Class (asOver G S)]

variable (S G) in
/-- The characters of the group scheme `G` over `S` are the group morphisms `G ⟶/S 𝔾ₘ[S]`. -/
abbrev char := Additive <| Grp_.mk' (asOver G S) ⟶ .mk' <| asOver 𝔾ₘ[S] S

variable (S G) in
/-- The cocharacters of the group scheme `G` over `S` are the group morphisms `𝔾ₘ[S] ⟶/S G`. -/
abbrev cochar := Additive <| Grp_.mk' (asOver 𝔾ₘ[S] S) ⟶ .mk' (asOver G S)

@[inherit_doc] notation "X("S", "G")" => char S G
@[inherit_doc] notation "X*("S", "G")" => cochar S G

end Grp_Class

section CommGrp_Class
variable [CommGrp_Class (asOver G S)]

/-- The perfect pairing between characters and cocharacters, valued in the characters of the
algebraic torus. -/
noncomputable def charPairing : X*(S, G) →+ X(S, G) →+ X(S, 𝔾ₘ[S]) where
  toFun χ := ((CommGrp_.yonedaCommGrpGrp.obj (.mk' <| asOver 𝔾ₘ[S] S)).map χ.op).hom.toAdditive
  map_zero' := by ext f; dsimp; ext : 1; exact ((yonedaGrp.map f).app _).hom.map_one
  map_add' χ χ' := by
    ext f : 2
    refine Mon_.Hom.ext ?_
    simpa using ((yonedaGrp.map f).app _).hom.map_mul χ.hom χ'.hom

end CommGrp_Class
end general_base

section IsDomain
variable {R : CommRingCat.{u}} [IsDomain R] {σ : Type u} {G : Scheme.{u}} [G.Over (Spec R)]

section AddCommGroup
variable {G : Type u} [AddCommGroup G]

/-- Characters of a diagonal group scheme over a domain are exactly the input group.

Note: This is true over a general ring using Cartier duality, but we do not prove that. -/
def charGrpAlg : X(Spec R, Spec <| .of R[G]) ≃+ G := sorry

/-- Cocharacters of a diagonal group scheme over a domain are exactly the dual of the input group.

Note: This is true over a general ring using Cartier duality, but we do not prove that. -/
def cocharGrpAlg : X*(Spec R, Spec <| .of R[G]) ≃+ (G →+ ℤ) := sorry

end AddCommGroup

/-- Characters of the algebraic circle with dimensions `σ`over a domain `R` are exactly `ℤ^σ`.

Note: This is true over a general base using Cartier duality, but we do not prove that. -/
def charTorus : X(Spec R, 𝔾ₘ[Spec R, σ]) ≃+ (σ → ℤ) := sorry

/-- Cocharacters of the algebraic circle with dimensions `σ`over a domain `R` are exactly `ℤ^σ`.

Note: This is true over a general base using Cartier duality, but we do not prove that. -/
def cocharTorus : X*(Spec R, 𝔾ₘ[Spec R, σ]) ≃+ (σ → ℤ) := sorry

section CommGrp_Class
variable [CommGrp_Class (asOver G (Spec R))]

/-- The `ℤ`-valued perfect pairing between characters and cocharacters of group schemes over a
domain.

Note: This exists over a general base using Cartier duality, but we do not prove that.  -/
noncomputable def charPairingInt : X*(Spec R, G) →+ X(Spec R, G) →+ ℤ :=
  .comp (AddMonoidHom.postcompAddEquiv <|
    (charTorus (R := R) (σ := PUnit)).trans (.piUnique _)).toAddMonoidHom charPairing

end CommGrp_Class
end IsDomain
end AlgebraicGeometry.Scheme
