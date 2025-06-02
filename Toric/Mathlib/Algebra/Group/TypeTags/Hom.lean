import Mathlib.Algebra.Group.Hom.Basic
import Mathlib.Algebra.Group.TypeTags.Hom

@[simp]
lemma AddMonoidHom.toMultiplicative_add
    {M N : Type*} [AddCommGroup M] [AddCommGroup N] (f g : M →+ N) :
    (f + g).toMultiplicative = f.toMultiplicative * g.toMultiplicative := rfl
