import Mathlib.Algebra.Algebra.Hom

@[simp]
lemma AlgHomClass.toAlgHom_toRingHom {R A B : Type*} [CommSemiring R] [Semiring A]
    [Semiring B] [Algebra R A] [Algebra R B] {F : Type*} [FunLike F A B] [AlgHomClass F R A B]
    (f : F) : (RingHomClass.toRingHom (AlgHomClass.toAlgHom f)) = RingHomClass.toRingHom f := rfl
