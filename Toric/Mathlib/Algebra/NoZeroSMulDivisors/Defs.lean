import Mathlib.Algebra.Group.Torsion
import Mathlib.Algebra.NoZeroSMulDivisors.Defs

variable {G M : Type*}

instance IsAddTorsionFree.to_noZeroSMulDivisors_nat [AddMonoid M] [IsAddTorsionFree M] :
    NoZeroSMulDivisors ℕ M where
  eq_zero_or_eq_zero_of_smul_eq_zero {n x} hx := by
    contrapose! hx; simpa using (nsmul_right_injective hx.1).ne hx.2

instance IsAddTorsionFree.to_noZeroSMulDivisors_int [AddGroup G] [IsAddTorsionFree G] :
    NoZeroSMulDivisors ℤ G where
  eq_zero_or_eq_zero_of_smul_eq_zero {n x} hx := by
    contrapose! hx; simpa using (zsmul_right_injective hx.1).ne hx.2

@[simp]
lemma noZeroSMulDivisors_nat_iff_isAddTorsionFree [AddCommGroup G] :
    NoZeroSMulDivisors ℕ G ↔ IsAddTorsionFree G where
  mp _ := by
    refine ⟨fun n hn a b hab ↦ ?_⟩
    simp only [← sub_eq_zero (a := n • a), ← nsmul_sub] at hab
    simpa [sub_eq_zero] using (smul_eq_zero_iff_right hn).1 hab
  mpr _ := inferInstance

@[simp]
lemma noZeroSMulDivisors_int_iff_isAddTorsionFree [AddCommGroup G] :
    NoZeroSMulDivisors ℤ G ↔ IsAddTorsionFree G where
  mp _ := by
    refine ⟨fun n hn a b hab ↦ ?_⟩
    simp only [← sub_eq_zero (a := (n : ℤ) • a), ← zsmul_sub, ← natCast_zsmul] at hab
    simpa [sub_eq_zero] using (smul_eq_zero_iff_right <| Int.natCast_ne_zero.2 hn).1 hab
  mpr _ := inferInstance

alias ⟨IsAddTorsionFree.of_noZeroSMulDivisors_nat, _⟩ := noZeroSMulDivisors_nat_iff_isAddTorsionFree
alias ⟨IsAddTorsionFree.of_noZeroSMulDivisors_int, _⟩ := noZeroSMulDivisors_int_iff_isAddTorsionFree
