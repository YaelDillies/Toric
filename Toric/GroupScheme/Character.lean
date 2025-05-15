/-
Copyright (c) 2025 Yaël Dillies, Michał Mrugała. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Michał Mrugała
-/
import Toric.GroupScheme.Torus

/-!
# The lattices of characters and cocharacters
-/

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Over
variable {S : Scheme} {G : Over S}

section Grp_Class
variable [Grp_Class G]

variable (G) in
abbrev char := Grp_.mk' G ⟶ .mk' <| .mk (𝔾ₘ[S] ↘ S)

variable (G) in
abbrev cochar := Grp_.mk' (.mk (𝔾ₘ[S] ↘ S)) ⟶ .mk' G

notation "X("G")" => char G
notation "X*("G")" => cochar G

end Grp_Class

section CommGrp_Class
variable [CommGrp_Class G]

/-- The perfect pairing between characters and cocharacters. -/
noncomputable def charPairing : X*(G) →* X(G) →* X(.mk (𝔾ₘ[S] ↘ S)) where
  toFun χ := ((CommGrp_.yonedaCommGrpGrp.obj (CommGrp_.mk' <| Over.mk (𝔾ₘ[S] ↘ S))).map χ.op).hom
  map_one' := by ext f; dsimp; ext : 1; exact ((yonedaGrp.map f).app _).hom.map_one
  map_mul' χ χ' := by
    ext f : 2
    refine Mon_.Hom.ext ?_
    simpa using ((yonedaGrp.map f).app _).hom.map_mul χ.hom χ'.hom

def charPairingInt : X*(G) →* X(G) →* ℤ := sorry

end CommGrp_Class
end AlgebraicGeometry.Scheme.Over
