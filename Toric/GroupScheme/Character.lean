/-
Copyright (c) 2025 Yaël Dillies, Michał Mrugała. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Michał Mrugała
-/

import Toric.GroupScheme.TorusCommGrp

open AlgebraicGeometry CategoryTheory

section
attribute [local instance] ChosenFiniteProducts.ofFiniteProducts
variable {S : Scheme} {G : Over S} [Grp_Class G]

variable (G) in
abbrev SchemeOver.characterGroup :=
  Grp_.mk' G ⟶ Grp_.mk' <| .mk (𝔾ₘ[S] ↘ S)

notation "X("G")" => SchemeOver.characterGroup G

end
