import Mathlib.Algebra.Group.Hom.Basic
import Mathlib.Algebra.Group.TypeTags.Hom

variable {M N : Type*} [AddMonoid M]

section AddMonoid
variable [AddMonoid N]

@[simp]
lemma AddMonoidHom.toMultiplicative_id :
    (AddMonoidHom.id M).toMultiplicative = .id (Multiplicative M) := rfl

end AddMonoid

variable [AddCommMonoid N]

@[simp]
lemma AddMonoidHom.toMultiplicative_add (f g : M →+ N) :
    (f + g).toMultiplicative = f.toMultiplicative * g.toMultiplicative := rfl
