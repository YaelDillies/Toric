import Mathlib.Data.Nat.Cast.Basic

lemma ofNat_nsmul_eq_mul {R : Type*} [Semiring R] (n : ℕ) [n.AtLeastTwo] (a : R) :
    ofNat(n) • a = ofNat(n) * a := by simp [nsmul_eq_mul]
