/-
Copyright (c) 2025 Yaël Dillies, Michał Mrugała, Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Michał Mrugała, Andrew Yang
-/
import Mathlib.FieldTheory.Separable
import Toric.GroupScheme.Torus
import Toric.Mathlib.Algebra.FreeAbelianGroup.Finsupp
import Toric.Mathlib.Algebra.Group.Equiv.Basic
import Toric.Mathlib.GroupTheory.FreeAbelianGroup
import Toric.Mathlib.LinearAlgebra.PerfectPairing.Basic

/-!
# The lattices of characters and cocharacters
-/

noncomputable section

open AddMonoidAlgebra CategoryTheory
open scoped Hom

namespace AlgebraicGeometry.Scheme
universe u

section general_base
variable {σ : Type u} {S G : Scheme.{u}} [G.Over S]

section Grp_Class
variable [Grp_Class (G.asOver S)]

variable (S G) in
/-- The characters of the group scheme `G` over `S` are the group morphisms `G ⟶/S 𝔾ₘ[S]`. -/
abbrev Char := HomGrp G 𝔾ₘ[S] S

variable (S G) in
/-- The cocharacters of the group scheme `G` over `S` are the group morphisms `𝔾ₘ[S] ⟶/S G`. -/
abbrev Cochar := HomGrp 𝔾ₘ[S] G S

@[inherit_doc] notation "X("S", "G")" => Char S G
@[inherit_doc] notation "X*("S", "G")" => Cochar S G

end Grp_Class

section CommGrp_Class
variable [CommGrp_Class (G.asOver S)]

/-- The perfect pairing between characters and cocharacters, valued in the characters of the
algebraic torus. -/
@[simps]
noncomputable def charPairingAux : X*(S, G) →+ X(S, G) →+ X(S, 𝔾ₘ[S]) where
  toFun χ :=
  { toFun χ' := χ.comp χ', map_zero' := by simp, map_add' := by simp [HomGrp.add_comp] }
  map_zero' := by ext f; simp
  map_add' χ χ' := by ext; simp [HomGrp.comp_add]

end CommGrp_Class
end general_base

section IsDomain
variable {R : CommRingCat.{u}} [IsDomain R] {σ : Type u} {G : Scheme.{u}} [G.Over (Spec R)]

section AddCommGroup
variable {G : Type u} [AddCommGroup G]

variable (R G) in
/-- Characters of a diagonal group scheme over a domain are exactly the input group.

Note: This is true over a general base using Cartier duality, but we do not prove that. -/
def charDiag : X(Spec R, Diag (Spec R) G) ≃+ G :=
  diagHomEquiv.symm.trans <| FreeAbelianGroup.liftAddEquiv.symm.trans <| .piUnique fun _ ↦ G

lemma charDiag_symm_apply (g : G) :
    (charDiag R G).symm g = diagHomGrp _ (FreeAbelianGroup.lift fun _ ↦ g) := rfl

lemma charDiag_diagHomGrp (f : _ →+ G) : charDiag R G (diagHomGrp _ f) = f (.of 0) := by
  apply (charDiag R G).symm.injective
  simp [charDiag_symm_apply]
  congr 1
  ext
  simp only [FreeAbelianGroup.lift.of]

variable (R G) in
/-- Cocharacters of a diagonal group scheme over a domain are exactly the dual of the input group.

Note: This is true over a general base using Cartier duality, but we do not prove that. -/
def cocharDiag : X*(Spec R, Diag (Spec R) G) ≃+ (G →+ ℤ) :=
  diagHomEquiv.symm.trans <| AddMonoidHom.postcompAddEquiv <| FreeAbelianGroup.uniqueEquiv _

lemma cocharDiag_symm_apply (g : G →+ ℤ) :
  (cocharDiag R G).symm g =
    diagHomGrp _ ((FreeAbelianGroup.uniqueEquiv _).symm.toAddMonoidHom.comp g) := rfl

end AddCommGroup

variable (R σ) in
/-- Characters of the algebraic torus with dimensions `σ`over a domain `R` are exactly `ℤ^σ`.

Note: This is true over a general base using Cartier duality, but we do not prove that. -/
def charTorus : X(Spec R, 𝔾ₘ[Spec R, σ]) ≃+ (σ →₀ ℤ) :=
  (charDiag R _).trans (FreeAbelianGroup.equivFinsupp _)

variable (R) in
def charTorusUnit : X(Spec R, 𝔾ₘ[Spec R]) ≃+ ℤ :=
  (charDiag R _).trans (FreeAbelianGroup.uniqueEquiv _)

variable (R σ) in
/-- Cocharacters of the algebraic torus with dimensions `σ`over a domain `R` are exactly `ℤ^σ`.

Note: This is true over a general base using Cartier duality, but we do not prove that. -/
def cocharTorus : X*(Spec R, 𝔾ₘ[Spec R, σ]) ≃+ (σ → ℤ) :=
  (cocharDiag R _).trans ⟨FreeAbelianGroup.lift.symm, fun _ _ ↦ rfl⟩

section CommGrp_Class
variable [CommGrp_Class (G.asOver (Spec R))]

variable (R G) in
attribute [local instance 1000000] AddEquivClass.instAddHomClass AddMonoidHomClass.toAddHomClass
  AddEquivClass.instAddMonoidHomClass in
attribute [-simp] charPairingAux_apply_apply in
/-- The `ℤ`-valued perfect pairing between characters and cocharacters of group schemes over a
domain.

Note: This exists over a general base using Cartier duality, but we do not prove that.  -/
noncomputable def charPairing : X*(Spec R, G) →ₗ[ℤ] X(Spec R, G) →ₗ[ℤ] ℤ where
  toFun x :=
  { toFun y := charTorusUnit (R := R) (charPairingAux (S := Spec R) (G := G) x y)
    map_add' _ _ := by simp only [map_add]
    map_smul' _ _ := by simp only [map_zsmul, smul_eq_mul, eq_intCast, Int.cast_eq] }
  map_add' _ _ := by ext; simp only [map_add, AddMonoidHom.add_apply, LinearMap.coe_mk,
    AddHom.coe_mk, LinearMap.add_apply]
  map_smul' _ _ := by ext; simp only [map_zsmul, AddMonoidHom.coe_smul, Pi.smul_apply, smul_eq_mul,
    LinearMap.coe_mk, AddHom.coe_mk, eq_intCast, Int.cast_eq, LinearMap.smul_apply]

instance isPerfPair_charPairing [Finite σ] : (charPairing R 𝔾ₘ[Spec R, σ]).IsPerfPair := by
  refine .congr (.id (R := ℤ) (M := Module.Dual ℤ (σ →₀ ℤ)))
    ((cocharTorus (R := R) (σ := σ)).trans (Finsupp.lift ..)).toIntLinearEquiv
    (charTorus (R := R) (σ := σ)).toIntLinearEquiv _ ?_
  ext f x
  apply (charTorusUnit (R := R)).symm.injective
  apply Additive.ofMul.symm.injective
  dsimp [charDiag_symm_apply, charPairing, charTorusUnit, charTorus, cocharTorus,
    cocharDiag_symm_apply]
  simp only [Char, AddEquiv.symm_apply_apply, diagHomGrp_comp, charDiag_diagHomGrp]
  simp only [PUnit.zero_eq, AddMonoidHom.coe_comp, AddMonoidHom.coe_coe, Function.comp_apply,
    FreeAbelianGroup.lift.of, EmbeddingLike.apply_eq_iff_eq, Finsupp.toFreeAbelianGroup_single]
  congr! 4 with x
  erw [Finsupp.toFreeAbelianGroup_single]
  simp

end CommGrp_Class
end IsDomain
end AlgebraicGeometry.Scheme
