import Mathlib.CategoryTheory.ChosenFiniteProducts
import Mathlib.CategoryTheory.Limits.FullSubcategory
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal

namespace CategoryTheory

universe v v₁ v₂ v₃ u u₁ u₂ u₃

open Limits ChosenFiniteProducts

namespace Functor

open LaxMonoidal Monoidal

variable {C : Type u} [Category.{v} C] [ChosenFiniteProducts C]
  {D : Type u₁} [Category.{v₁} D] [ChosenFiniteProducts D]
  {E : Type u₃} [Category.{v₃} E] [ChosenFiniteProducts E]
  (F : C ⥤ D) [PreservesFiniteProducts F]
  (G : D ⥤ E) [PreservesFiniteProducts G]

attribute [local instance] monoidalOfChosenFiniteProducts

attribute [instance] NatTrans.monoidal_of_preservesFiniteProducts

lemma ε_of_chosenFiniteProducts : ε F = (preservesTerminalIso F).inv := by
  change (εIso F).symm.inv = _; congr; ext; simp; rfl

lemma μ_of_chosenFiniteProducts (X Y : C) : μ F X Y = (prodComparisonIso F X Y).inv := by
  change (μIso F X Y).symm.inv = _; congr; ext : 1; rfl

@[simp]
lemma preservesTerminalIso_id : preservesTerminalIso (𝟭 C) = .refl _ := by
  ext; exact toUnit_unique ..

@[simp]
lemma preservesTerminalIso_comp :
    preservesTerminalIso (F ⋙ G) =
      G.mapIso (preservesTerminalIso F) ≪≫ preservesTerminalIso G := by
  ext; exact toUnit_unique ..

@[simp]
lemma prodComparisonIso_id (X Y : C) : prodComparisonIso (𝟭 C) X Y = .refl _ := by
  ext <;> simp

@[simp]
lemma prodComparisonIso_comp (X Y : C) :
    prodComparisonIso (F ⋙ G) X Y =
      G.mapIso (prodComparisonIso F X Y) ≪≫ prodComparisonIso G (F.obj X) (F.obj Y) := by
  ext <;> simp [ChosenFiniteProducts.prodComparison, ← G.map_comp]

-- TODO: Rename
alias map_toUnit_comp_terminalComparison := map_toUnit_comp_terminalCompariso

end CategoryTheory.Functor

namespace CategoryTheory.ChosenFiniteProducts
universe u v
variable {C : Type u} [Category.{v} C] [ChosenFiniteProducts C] {P : C → Prop}

open Limits MonoidalCategory

-- TODO: Rename
alias associator_inv_fst_fst := associator_inv_fst

-- TODO: Introduce `ClosedUnderFiniteProducts`?
noncomputable def fullSubcategory (hP₀ : ClosedUnderLimitsOfShape (Discrete PEmpty) P)
    (hP₂ : ClosedUnderLimitsOfShape (Discrete WalkingPair) P) :
    ChosenFiniteProducts (FullSubcategory P) where
  product X Y := {
    cone := BinaryFan.mk
      (P := ⟨X.1 ⊗ Y.1, hP₂ (product X.obj Y.obj).isLimit <| by rintro ⟨_ | _⟩ <;> simp [X.2, Y.2]⟩)
      (fst X.1 Y.1) (snd X.1 Y.1)
    isLimit := isLimitOfReflectsOfMapIsLimit (fullSubcategoryInclusion _) _ _ <|
      (product X.obj Y.obj).isLimit.ofIsoLimit <| isoBinaryFanMk _
  }
  terminal.cone := asEmptyCone ⟨𝟙_ C, hP₀ terminal.isLimit <| by simp⟩
  terminal.isLimit := IsTerminal.isTerminalOfObj (fullSubcategoryInclusion _) _ <| .ofUnique (𝟙_ C)

end CategoryTheory.ChosenFiniteProducts

namespace CategoryTheory.Functor.EssImageSubcategory

open Limits ChosenFiniteProducts MonoidalCategory

universe u₁ u₂ v₁ v₂
variable {C : Type u₁} [Category.{v₁} C] [ChosenFiniteProducts C]
variable {D : Type u₂} [Category.{v₂} D] [ChosenFiniteProducts D]
variable (F : C ⥤ D) [PreservesFiniteProducts F] [F.Full] [F.Faithful]
  {T X Y Z : F.EssImageSubcategory}

@[simps!]
noncomputable instance instChosenFiniteProducts : ChosenFiniteProducts F.EssImageSubcategory :=
  .fullSubcategory (.essImage _) (.essImage _)

lemma tensor_obj (X Y : F.EssImageSubcategory) : (X ⊗ Y).obj = X.obj ⊗ Y.obj := rfl

lemma fst_def (X Y : F.EssImageSubcategory) : fst X Y = fst X.obj Y.obj := rfl
lemma snd_def (X Y : F.EssImageSubcategory) : snd X Y = snd X.obj Y.obj := rfl

lemma whiskerLeft_def (X : F.EssImageSubcategory) (f : Y ⟶ Z) : X ◁ f = X.obj ◁ f := by
  ext
  · erw [whiskerLeft_fst, whiskerLeft_fst]
    simp [fst_def]
  · erw [whiskerLeft_snd, whiskerLeft_snd]
    simp [snd_def]
    rfl

lemma whiskerRight_def (f : Y ⟶ Z) (X : F.EssImageSubcategory) :
    f ▷ X = MonoidalCategoryStruct.whiskerRight (C := D) f X.obj := by
  ext
  · erw [whiskerRight_fst, whiskerRight_fst]
    rfl
  · erw [whiskerRight_snd, whiskerRight_snd]
    rfl

lemma associator_hom_def (X Y Z : F.EssImageSubcategory) :
    (α_ X Y Z).hom = (α_ X.obj Y.obj Z.obj).hom := by
  ext
  · erw [associator_hom_fst, associator_hom_fst]
    rfl
  · simp only [Category.assoc, associator_hom_snd_fst]
    erw [associator_hom_snd_fst]
    rfl
  · simp only [Category.assoc, associator_hom_snd_snd]
    erw [associator_hom_snd_snd]
    rfl

lemma associator_inv_def (X Y Z : F.EssImageSubcategory) :
    (α_ X Y Z).inv = (α_ X.obj Y.obj Z.obj).inv := by
  ext
  · simp only [Category.assoc, associator_inv_fst_fst]
    erw [associator_inv_fst_fst]
    rfl
  · simp only [Category.assoc, associator_inv_fst_snd]
    erw [associator_inv_fst_snd]
    rfl
  · erw [associator_inv_snd, associator_inv_snd]
    rfl

lemma lift_def (f : T ⟶ X) (g : T ⟶ Y) : lift f g = lift (T := T.1) f g := by
  ext
  · erw [lift_fst, lift_fst]
  · erw [lift_snd, lift_snd]

lemma toUnit_def (X : F.EssImageSubcategory) : toUnit X = toUnit X.obj := toUnit_unique ..

end CategoryTheory.Functor.EssImageSubcategory
