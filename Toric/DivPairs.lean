/-
Copyright (c) 2025 Yaël Dillies, Michał Mrugała. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Michał Mrugała
-/
import Mathlib.GroupTheory.MonoidLocalization.Basic

/-!
# Submonoid of pairs with quotient in a submonoid

This file defines the submonoid of pairs whose quotient lies in a submonoid of the localization.
-/

variable {M G : Type*} [CommMonoid M] [CommGroup G]
  {f : (⊤ : Submonoid M).LocalizationMap G} {s : Submonoid G} {x : M × M}

namespace Submonoid

variable (f s) in
/-- The submonoid of pairs whose quotient lies in a submonoid of the localization. -/
@[to_additive "The submonoid of pairs whose difference lie in a submonoid of the localization."]
def divPairs : Submonoid (M × M) := s.comap <| divMonoidHom.comp <| f.toMap.prodMap f.toMap

@[to_additive (attr := simp)]
lemma mem_divPairs : x ∈ divPairs f s ↔ f.toMap x.1 / f.toMap x.2 ∈ s := .rfl

end Submonoid
