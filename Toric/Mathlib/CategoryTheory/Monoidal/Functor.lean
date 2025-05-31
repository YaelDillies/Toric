import Mathlib.CategoryTheory.Monoidal.Functor

namespace CategoryTheory.Functor
variable {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]

open MonoidalCategory

namespace LaxMonoidal
variable (F : C ⥤ D) [F.LaxMonoidal]

@[reassoc]
lemma wiskerLeft_left_unitality {X : C} {Y : D} (f : Y ⟶ F.obj X) :
    𝟙_ D ◁ f ≫ (λ_ (F.obj X)).hom = (ε F ⊗ f) ≫ μ F (𝟙_ C) X ≫ F.map (λ_ X).hom := by
  rw [left_unitality]; simp [tensorHom_def']

@[reassoc]
lemma wiskerRight_right_unitality {X : C} {Y : D} (f : Y ⟶ F.obj X) :
    f ▷ 𝟙_ D ≫ (ρ_ (F.obj X)).hom = (f ⊗ ε F) ≫ μ F X (𝟙_ C) ≫ F.map (ρ_ X).hom := by
  rw [right_unitality]; simp [tensorHom_def]

end LaxMonoidal

open LaxMonoidal OplaxMonoidal

namespace Monoidal

@[simp]
lemma inv_μ (F : C ⥤ D) [F.Monoidal] (X Y : C) : CategoryTheory.inv (μ F X Y) = δ F X Y := by
  rw [← Monoidal.μIso_inv, ← CategoryTheory.IsIso.inv_eq_inv]
  simp only [IsIso.inv_inv, IsIso.Iso.inv_inv, μIso_hom]

@[simp]
lemma inv_δ (F : C ⥤ D) [F.Monoidal] (X Y : C) : CategoryTheory.inv (δ F X Y) = μ F X Y := by
  simp [← inv_μ]

end CategoryTheory.Functor.Monoidal
