/-
Copyright (c) 2025 Yaël Dillies, Michał Mrugała. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Michał Mrugała
-/
import Mathlib

/-!
# Group-like elements in a bialgebra
-/

open CoalgebraStruct

variable {F R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]
  [Coalgebra R A] [Coalgebra R B]

namespace Coalgebra

variable (R) in
/--  A group-like element in a coalgebra is a unit `a` such that `Δ a = a ⊗ₜ a`. -/
structure IsGroupLikeElem (a : A) where
  isUnit : IsUnit a
  comul_eq_tmul_self : comul (R := R) a = a ⊗ₜ a

lemma IsGroupLikeElem.map [FunLike F A B] [BialgHomClass F R A B] (f : F) {a : A}
    (ha : IsGroupLikeElem R a) : IsGroupLikeElem R (f a) where
  isUnit := ha.isUnit.map f
  comul_eq_tmul_self := by
    rw [← CoalgHomClass.map_comp_comul_apply, ha.comul_eq_tmul_self]
    simp

end Coalgebra
