/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jens Wagemaker, Yaël Dillies
-/
import Mathlib.Algebra.Group.Units.Defs
import Mathlib.Logic.Basic

/-!
# Irreducible elements in a monoid

This file defines irreducible elements of a monoid, as non-units that can't be written as the sum of
two non-units. This generalises irreducible elements of a ring.

In decomposition monoids (e.g., `ℕ`, `ℤ`), this predicate is equivalent to `Prime`
(see `irreducible_iff_prime`), however this is not true in general.
-/

assert_not_exists MonoidWithZero OrderedCommMonoid Multiset

variable {M : Type*}

/-- `AddIrreducible p` states that `p` is non-unit and only factors into units. -/
structure AddIrreducible [AddMonoid M] (p : M) : Prop where
  /-- An irreducible element is not a unit. -/
  not_isAddUnit : ¬IsAddUnit p
  /-- If an irreducible elements factors, then one factor is a unit. -/
  isAddUnit_or_isAddUnit ⦃a b⦄ : p = a + b → IsAddUnit a ∨ IsAddUnit b

section AddMonoid
variable [AddMonoid M] {p q x y : M}

lemma addIrreducible_iff :
    AddIrreducible p ↔ ¬IsAddUnit p ∧ ∀ ⦃a b⦄, p = a + b → IsAddUnit a ∨ IsAddUnit b where
  mp hp := ⟨hp.not_isAddUnit, hp.isAddUnit_or_isAddUnit⟩
  mpr hp := ⟨hp.1, hp.2⟩

@[simp]
lemma not_addIrreducible_zero : ¬AddIrreducible (0 : M) := by simp [addIrreducible_iff]

lemma AddIrreducible.ne_zero (hp : AddIrreducible p) : p ≠ 0 := by
  rintro rfl; exact not_addIrreducible_zero hp

lemma of_addIrreducible_add : AddIrreducible (x + y) → IsAddUnit x ∨ IsAddUnit y | ⟨_, h⟩ => h rfl

lemma addIrreducible_or_factor (hp : ¬IsAddUnit p) :
    AddIrreducible p ∨ ∃ a b, ¬IsAddUnit a ∧ ¬IsAddUnit b ∧ p = a + b := by
  simpa [addIrreducible_iff, hp, and_rotate] using em (∀ a b, p = a + b → IsAddUnit a ∨ IsAddUnit b)

end AddMonoid
