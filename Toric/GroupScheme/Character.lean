/-
Copyright (c) 2025 Yaël Dillies, Michał Mrugała. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Michał Mrugała
-/

import Toric.GroupScheme.TorusCommGrp

open AlgebraicGeometry CategoryTheory

instance {C : Type*} [Category C] [ChosenFiniteProducts C] (X : C) [CommGrp_Class X] :
  CommGrp_Class (Grp_.mk' X).X := ‹_›

attribute [local instance] ChosenFiniteProducts.ofFiniteProducts
section

variable {S : Scheme} {G : Over S} [Grp_Class G]

variable (G) in
abbrev SchemeOver.char :=
  Grp_.mk' G ⟶ Grp_.mk' <| .mk (𝔾ₘ[S] ↘ S)

notation "X("G")" => SchemeOver.char G

variable (G) in
abbrev SchemeOver.cochar :=
  (Grp_.mk' <| .mk (𝔾ₘ[S] ↘ S)) ⟶ Grp_.mk' G

end

section

variable (G : Type*)

@[ext] lemma addToMulExt {a b : Additive G} (h : a.toMul = b.toMul) : a = b := h

end

section

variable {S : Scheme} {G : Over S} [CommGrp_Class G]


noncomputable def SchemeOver.charPairing :
    cochar G →* X(G) →* X(.mk (𝔾ₘ[S] ↘ S)) := sorry

def SchemeOver.charPairingInt : SchemeOver.char G →* SchemeOver.cochar G →* ℤ := sorry

end
