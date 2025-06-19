import Mathlib.CategoryTheory.Comma.Over.OverClass

namespace CategoryTheory.OverClass
variable {C : Type*} [Category C] {X Y Z S : C} [OverClass X S] [OverClass Y S] [OverClass Z S]

instance (f : X ⟶ Y) [IsIso f] [HomIsOver f S] : IsIso (asOverHom S f) :=
  have : IsIso ((Over.forget S).map (asOverHom S f)) := ‹_›
  isIso_of_reflects_iso _ (Over.forget _)

instance {f : X ⟶ Y} [IsIso f] [HomIsOver f S] : HomIsOver (asIso f).hom S := ‹_›
instance {f : X ⟶ Y} [IsIso f] [HomIsOver f S] : HomIsOver (asIso f).inv S where
instance {f : X ⟶ Y} [IsIso f] [HomIsOver f S] : HomIsOver (inv f) S where

@[simp] lemma asOverHom_id : asOverHom S (𝟙 X) = 𝟙 (asOver X S) := rfl

@[simp] lemma asOverHom_comp (f : X ⟶ Y) (g : Y ⟶ Z) [HomIsOver f S] [HomIsOver g S] :
    asOverHom S (f ≫ g) = asOverHom S f ≫ asOverHom S g := rfl

@[simp] lemma asOverHom_inv (f : X ⟶ Y) [IsIso f] [HomIsOver f S] :
    asOverHom S (inv f) = inv (asOverHom S f) := by simp [← hom_comp_eq_id, ← asOverHom_comp]

end CategoryTheory.OverClass
