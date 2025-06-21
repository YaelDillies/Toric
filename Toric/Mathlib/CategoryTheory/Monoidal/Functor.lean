import Mathlib.CategoryTheory.Monoidal.Functor

namespace CategoryTheory.Functor
variable {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]

open MonoidalCategory

namespace LaxMonoidal
variable (F : C ⥤ D) [F.LaxMonoidal]

@[reassoc]
lemma tensorHom_ε_left_μ {X : C} {Y : D} (f : Y ⟶ F.obj X) :
    (ε F ⊗ₘ f) ≫ μ F (𝟙_ C) X = 𝟙_ D ◁ f ≫ (λ_ (F.obj X)).hom ≫ F.map (λ_ X).inv := by
  rw [left_unitality]; simp [tensorHom_def']

@[reassoc]
lemma tensorHom_ε_right_μ {X : C} {Y : D} (f : Y ⟶ F.obj X) :
    (f ⊗ₘ ε F) ≫ μ F X (𝟙_ C) = f ▷ 𝟙_ D ≫ (ρ_ (F.obj X)).hom ≫ F.map (ρ_ X).inv := by
  rw [right_unitality]; simp [tensorHom_def]

@[reassoc]
lemma wiskerLeft_left_unitality {X : C} {Y : D} (f : Y ⟶ F.obj X) :
    𝟙_ D ◁ f ≫ (λ_ (F.obj X)).hom = (ε F ⊗ₘ f) ≫ μ F (𝟙_ C) X ≫ F.map (λ_ X).hom := by
  rw [left_unitality]; simp [tensorHom_def']

@[reassoc]
lemma wiskerRight_right_unitality {X : C} {Y : D} (f : Y ⟶ F.obj X) :
    f ▷ 𝟙_ D ≫ (ρ_ (F.obj X)).hom = (f ⊗ₘ ε F) ≫ μ F X (𝟙_ C) ≫ F.map (ρ_ X).hom := by
  rw [right_unitality]; simp [tensorHom_def]

@[reassoc]
lemma whiskerRight_μ_μ (X Y Z : C) :
    μ F X Y ▷ F.obj Z ≫ μ F (X ⊗ Y) Z = (α_ (F.obj X) (F.obj Y) (F.obj Z)).hom ≫
      F.obj X ◁ μ F Y Z ≫ μ F X (Y ⊗ Z) ≫ F.map (α_ X Y Z).inv := by
  rw [← associativity_assoc, ← F.map_comp, Iso.hom_inv_id, map_id, Category.comp_id]

@[reassoc]
lemma whiskerLeft_μ_μ (X Y Z : C) :
    F.obj X ◁ μ F Y Z ≫ μ F X (Y ⊗ Z) = (α_ (F.obj X) (F.obj Y) (F.obj Z)).inv ≫
      μ F X Y ▷ F.obj Z ≫ μ F (X ⊗ Y) Z ≫ F.map (α_ X Y Z).hom := by
  rw [associativity, Iso.inv_hom_id_assoc]

end LaxMonoidal

namespace OplaxMonoidal
variable (F : C ⥤ D) [F.OplaxMonoidal]

@[reassoc]
lemma δ_tensorHom_η_left {X : C} {Y : D} (f : F.obj X ⟶ Y) :
    δ F (𝟙_ C) X ≫ (η F ⊗ₘ f) = F.map (λ_ X).hom ≫ (λ_ (F.obj X)).inv ≫ 𝟙_ D ◁ f := by
  rw [left_unitality]; simp [tensorHom_def]

@[reassoc]
lemma δ_tensorHom_η_right {X : C} {Y : D} (f : F.obj X ⟶ Y) :
    δ F X (𝟙_ C) ≫ (f ⊗ₘ η F) = F.map (ρ_ X).hom ≫ (ρ_ (F.obj X)).inv ≫ f ▷ 𝟙_ D := by
  rw [right_unitality]; simp [tensorHom_def']

@[reassoc]
lemma δ_whiskerRight_δ (X Y Z : C) :
    δ F (X ⊗ Y) Z ≫ δ F X Y ▷ F.obj Z = F.map (α_ X Y Z).hom ≫
      δ F X (Y ⊗ Z) ≫ F.obj X ◁ δ F Y Z ≫ (α_ (F.obj X) (F.obj Y) (F.obj Z)).inv := by
  rw [← associativity_assoc, Iso.hom_inv_id, Category.comp_id]

@[reassoc]
lemma δ_whiskerLeft_δ (X Y Z : C) :
    δ F X (Y ⊗ Z) ≫ F.obj X ◁ δ F Y Z = F.map (α_ X Y Z).inv ≫
      δ F (X ⊗ Y) Z ≫ δ F X Y ▷ F.obj Z ≫ (α_ (F.obj X) (F.obj Y) (F.obj Z)).hom := by
  rw [associativity, ← F.map_comp_assoc, Iso.inv_hom_id, Functor.map_id, Category.id_comp]

end OplaxMonoidal

open LaxMonoidal OplaxMonoidal

namespace Monoidal

variable (F : C ⥤ D) [F.Monoidal] (X Y : C)

@[simp]
lemma inv_η : CategoryTheory.inv (η F) = ε F := by
  rw [← εIso_hom, ← Iso.comp_inv_eq_id, εIso_inv, IsIso.inv_hom_id]

@[simp]
lemma inv_ε : CategoryTheory.inv (ε F) = η F := by
  simp [← inv_η]

@[simp]
lemma inv_μ : CategoryTheory.inv (μ F X Y) = δ F X Y := by
  rw [← Monoidal.μIso_inv, ← CategoryTheory.IsIso.inv_eq_inv]
  simp only [IsIso.inv_inv, IsIso.Iso.inv_inv, μIso_hom]

@[simp] lemma inv_δ : CategoryTheory.inv (δ F X Y) = μ F X Y := by simp [← inv_μ]

end CategoryTheory.Functor.Monoidal
