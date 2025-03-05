/-
Copyright (c) 2025 Michał Mrugała, Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michał Mrugała, Andrew Yang
-/
import Mathlib.CategoryTheory.Monoidal.Yoneda
import Toric.Mathlib.CategoryTheory.Monoidal.CommMon_

open CategoryTheory ChosenFiniteProducts MonoidalCategory Mon_Class Opposite

universe w v u

variable {C : Type*} [Category.{v} C] [ChosenFiniteProducts C]
variable (X : C)

section CommGrp_

--TODO: get rid of erw
/-- If `X` represents a presheaf of commutative groups, then `X` is a commutative group object. -/
def IsCommMon.ofRepresentableBy (F : Cᵒᵖ ⥤ CommMonCat.{w})
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

end CommGrp_
