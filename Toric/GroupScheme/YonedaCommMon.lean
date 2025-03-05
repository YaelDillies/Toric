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

variable (F : Cᵒᵖ ⥤ Grp)

-- TODO: rename Mon_ClassOfRepresentableBy to Mon_Class.ofRepresentableBy
/-- If `X` represents a presheaf of commutative groups, then `X` is a commutative group object. -/
def IsCommMon.ofRepresentableBy (F : Cᵒᵖ ⥤ CommMonCat.{w})
    (α : (F ⋙ forget _).RepresentableBy X) :
    letI := Mon_ClassOfRepresentableBy X (F ⋙ (forget₂ CommMonCat MonCat)) α
    IsCommMon X := by
  letI := Mon_ClassOfRepresentableBy X (F ⋙ (forget₂ CommMonCat MonCat)) α
  refine ⟨?_⟩
  change _ ≫ α.homEquiv.symm _ = α.homEquiv.symm _
  apply α.homEquiv.injective
  simp only [α.homEquiv_comp, Equiv.apply_symm_apply]
  simp only [Functor.comp_map, ConcreteCategory.forget_map_eq_coe, map_mul]
  rw [_root_.mul_comm]
  simp only [← Functor.comp_map, ← ConcreteCategory.forget_map_eq_coe, ← Functor.comp_obj,
        ← α.homEquiv_comp]
  simp
  sorry

end CommGrp_
