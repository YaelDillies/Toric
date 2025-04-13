import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts

namespace CategoryTheory.Limits
variable {C : Type*} [Category C]

@[simp]
lemma BinaryFan.ext_hom_hom {A B : C} {c c' : BinaryFan A B} (e : c.pt ≅ c'.pt)
    (h₁ : c.fst = e.hom ≫ c'.fst) (h₂ : c.snd = e.hom ≫ c'.snd) :
    (ext e h₁ h₂).hom.hom = e.hom := rfl

@[simp]
lemma BinaryCofan.ext_hom_hom {A B : C} {c c' : BinaryCofan A B} (e : c.pt ≅ c'.pt)
    (h₁ : c.inl ≫ e.hom = c'.inl) (h₂ : c.inr ≫ e.hom = c'.inr) :
    (ext e h₁ h₂).hom.hom = e.hom := rfl

end CategoryTheory.Limits
