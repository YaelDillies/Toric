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

attribute [local instance] ChosenFiniteProducts.ofFiniteProducts

section Grp_Class
variable [Grp_Class G]

variable (G) in
abbrev char := Grp_.mk' G ⟶ .mk' <| .mk (𝔾ₘ[S] ↘ S)

variable (G) in
abbrev cochar := Grp_.mk' (.mk (𝔾ₘ[S] ↘ S)) ⟶ .mk' G

notation "X("G")" => char G

end Grp_Class

section CommGrp_Class
variable [CommGrp_Class G]

noncomputable def charPairing : cochar G →* X(G) →* X(.mk (𝔾ₘ[S] ↘ S)) := sorry

def charPairingInt : char G →* cochar G →* ℤ := sorry

end CommGrp_Class
end AlgebraicGeometry.Scheme.Over
