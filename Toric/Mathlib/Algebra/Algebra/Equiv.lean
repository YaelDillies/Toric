import Mathlib.Algebra.Algebra.Equiv

variable {A B C D : Type*} [CommSemiring A] [Semiring B] [Algebra A B] [Semiring C] [Algebra A C]
  [Semiring D] [Algebra A D]

@[simp] lemma AlgEquiv.trans_symm_self (f : B ≃ₐ[A] C) : f.trans f.symm = .refl := by aesop
@[simp] lemma AlgEquiv.symm_trans_self (f : B ≃ₐ[A] C) : f.symm.trans f = .refl := by aesop

@[simp, norm_cast]
lemma AlgEquiv.toRingHom_refl : AlgEquiv.refl (R := A) (A₁ := B) = RingHom.id B := rfl

@[simp, norm_cast]
lemma AlgEquiv.toRingHom_trans (f : B ≃ₐ[A] C) (g : C ≃ₐ[A] D) :
    (f.trans g : B →+* D) = .comp g (f : B →+* C) := rfl
