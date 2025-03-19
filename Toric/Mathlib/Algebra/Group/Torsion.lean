/-
Copyright (c) 2025 Yaël Dillies, Patrick Luo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Patrick Luo
-/
import Mathlib.Algebra.Group.Basic
import Mathlib.Tactic.Common

/-!
# Torsion-free monoids and groups

## TODO

Replace
* `Monoid.IsTorsionFree`
* `MulAction.injective₀`
* `Ring.nsmul_right_injective`
-/

open Function

variable {M G : Type*}

variable (M) in
/-- A monoid is `R`-torsion-free if scalar multiplication by every non-zero element `a : R` is
injective. -/
@[mk_iff]
class IsAddTorsionFree [AddMonoid M] where
  protected nsmul_right_injective₀ ⦃n : ℕ⦄ (hn : n ≠ 0) : Injective fun x : M ↦ n • x

section Monoid
variable [Monoid M]

variable (M) in
/-- A monoid is `R`-torsion-free if power by every non-zero element `a : R` is injective. -/
@[to_additive, mk_iff]
class IsMulTorsionFree where
  protected pow_left_injective₀ ⦃n : ℕ⦄ (hn : n ≠ 0) : Injective fun x : M ↦ x ^ n

attribute [to_additive existing] isMulTorsionFree_iff

variable [IsMulTorsionFree M] {n : ℕ}

@[to_additive nsmul_right_injective₀]
lemma pow_left_injective₀ (hn : n ≠ 0) : Injective fun x : M ↦ x ^ n :=
  IsMulTorsionFree.pow_left_injective₀ hn

end Monoid

section Group
variable [Group G] [IsMulTorsionFree G]

@[to_additive zsmul_right_injective₀]
lemma zpow_left_injective₀ : ∀ {n : ℤ}, n ≠ 0 → Injective fun x : G ↦ x ^ n
  | (n + 1 : ℕ), _ => by
    simpa [← Int.natCast_one, ← Int.natCast_add] using pow_left_injective₀ n.succ_ne_zero
  | .negSucc n, _ => by simpa using inv_injective.comp (pow_left_injective₀ n.succ_ne_zero)

end Group
