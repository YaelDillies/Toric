import Mathlib.CategoryTheory.Monoidal.CommMon_
import Mathlib.CategoryTheory.Monoidal.Mon_
import Mathlib.CategoryTheory.Monoidal.Yoneda

universe v₁ v₂ u₁ u₂ u
open CategoryTheory ChosenFiniteProducts MonoidalCategory Mon_Class Opposite

variable {C : Type*} [Category C]

section CommMon_

variable (X : C) [ChosenFiniteProducts C]

/-- If `X` represents a presheaf of commutative groups, then `X` is a commutative group object. -/
lemma IsCommMon.ofRepresentableBy (F : Cᵒᵖ ⥤ CommMonCat)
    (α : (F ⋙ forget _).RepresentableBy X) :
    letI := Mon_ClassOfRepresentableBy X (F ⋙ (forget₂ CommMonCat MonCat)) α
    IsCommMon X := by
  letI := Mon_ClassOfRepresentableBy X (F ⋙ (forget₂ CommMonCat MonCat)) α
  refine ⟨?_⟩
  change (β_ X X).hom ≫ α.homEquiv.symm (α.homEquiv (fst X X) * α.homEquiv (snd X X))
      = α.homEquiv.symm (α.homEquiv (fst X X) * α.homEquiv (snd X X))
  apply α.homEquiv.injective
  simp only [α.homEquiv_comp, Equiv.apply_symm_apply]
  simp only [Functor.comp_map, ConcreteCategory.forget_map_eq_coe, map_mul]
  simp only [← ConcreteCategory.forget_map_eq_coe, ← Functor.comp_map, ← α.homEquiv_comp]
  rw [_root_.mul_comm]
  simp

end CommMon_
