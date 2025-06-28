import Mathlib.Algebra.Group.Equiv.Defs
import Mathlib.Algebra.Group.Hom.Basic
import Mathlib.Algebra.Group.TypeTags.Hom

variable {M N : Type*}

section AddMonoid
variable [AddMonoid M] [AddMonoid N]

@[simp]
lemma AddMonoidHom.toMultiplicative_id :
    (AddMonoidHom.id M).toMultiplicative = .id (Multiplicative M) := rfl

end AddMonoid

section AddCommMonoid
variable [AddMonoid M] [AddCommMonoid N]

@[simp]
lemma AddMonoidHom.toMultiplicative_add (f g : M →+ N) :
    (f + g).toMultiplicative = f.toMultiplicative * g.toMultiplicative := rfl

end AddCommMonoid

/-- `MonoidHom.toAdditive''` as a `MulEquiv`. -/
def MonoidHom.toAdditive''MulEquiv {M N : Type*} [AddMonoid M] [CommMonoid N] :
    (Multiplicative M →* N) ≃* Multiplicative (M →+ Additive N) where
  toEquiv := MonoidHom.toAdditive''.trans Multiplicative.ofAdd
  map_mul' _ _ := rfl
