import Mathlib.CategoryTheory.Monoidal.Functor

namespace CategoryTheory.Functor.Monoidal
variable {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]

open LaxMonoidal OplaxMonoidal

@[simp]
lemma inv_μ (F : C ⥤ D) [F.Monoidal] (X Y : C) : CategoryTheory.inv (μ F X Y) = δ F X Y := by
  rw [← Monoidal.μIso_inv, ← CategoryTheory.IsIso.inv_eq_inv]
  simp only [IsIso.inv_inv, IsIso.Iso.inv_inv, μIso_hom]

@[simp]
lemma inv_δ (F : C ⥤ D) [F.Monoidal] (X Y : C) : CategoryTheory.inv (δ F X Y) = μ F X Y := by
  simp [← inv_μ]

end CategoryTheory.Functor.Monoidal
