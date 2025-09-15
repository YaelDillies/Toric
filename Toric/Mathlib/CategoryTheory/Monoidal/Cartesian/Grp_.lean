/-
Copyright (c) 2025 Yaël Dillies, Michał Mrugała, Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Michał Mrugała, Andrew Yang
-/
import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp_
import Toric.Mathlib.CategoryTheory.Monoidal.Cartesian.Mon_
import Toric.Mathlib.CategoryTheory.Monoidal.Grp_

open CategoryTheory Mon_Class MonoidalCategory CartesianMonoidalCategory

/-! ### Internal groups -/

namespace Grp_
variable {C : Type*} [Category C] [CartesianMonoidalCategory C] [BraidedCategory C] {G H : Grp_ C}
  [IsCommMon H.X]

-- TODO: Make `Grp_.toMon_` an abbrev in mathlib.
set_option allowUnsafeReducibility true in
attribute [reducible] Grp_.toMon_
attribute [local simp] mul_comm mul_div_mul_comm

namespace Hom

instance : Mon_Class H where
  one := η[H.toMon_]
  mul := μ[H.toMon_]
  one_mul := Mon_Class.one_mul H.toMon_
  mul_one := Mon_Class.mul_one H.toMon_
  mul_assoc := Mon_Class.mul_assoc H.toMon_

@[simp] lemma hom_one : (1 : G ⟶ H).hom = 1 := rfl

@[simp] lemma hom_mul (f g : G ⟶ H) : (f * g).hom = f.hom * g.hom := rfl

@[simp] lemma hom_pow (f : G ⟶ H) (n : ℕ) : (f ^ n).hom = f.hom ^ n := by
  induction n <;> simp [pow_succ, *]

instance {f : G ⟶ H} : IsMon_Hom f.hom⁻¹ where

attribute [local simp] mul_eq_mul Grp_Class.inv_eq_inv comp_mul in
/-- A commutative group object is a group object in the category of group objects. -/
instance : Grp_Class H where inv := .mk ι[H.X]

@[simp] lemma hom_inv (f : G ⟶ H) : f⁻¹.hom = f.hom⁻¹ := rfl
@[simp] lemma hom_div (f g : G ⟶ H) : (f / g).hom = f.hom / g.hom := rfl
@[simp] lemma hom_zpow (f : G ⟶ H) (n : ℤ) : (f ^ n).hom = f.hom ^ n := by cases n <;> simp

end Hom

attribute [local simp] mul_eq_mul comp_mul in
/-- A commutative group object is a commutative group object in the category of group objects. -/
instance : IsCommMon H where

instance {C : Type*} [Category C] [CartesianMonoidalCategory C] [BraidedCategory C]
    {G H : Grp_ C} [IsCommMon G.X] [IsCommMon H.X] (f : G ⟶ H) : IsMon_Hom f where
  one_hom := by ext; simp [Grp_.Hom.instMon_Class_toric]
  mul_hom := by ext; simp [Grp_.Hom.instMon_Class_toric]

end Grp_

/-! ### Random lemmas -/

section
variable {C : Type*} [Category C] [CartesianMonoidalCategory C] {G X : C} [Grp_Class G]

@[simp]
lemma Grp_.homMk_hom' {G H : Grp_ C} (f : G ⟶ H) : homMk (G := G.X) (H := H.X) f.hom = f := rfl

lemma Grp_Class.inv_eq_comp_inv (f : X ⟶ G) : f ≫ ι = f⁻¹ := rfl

lemma Grp_Class.mul_eq_comp_mul (f g : X ⟶ G) : f * g = lift f g ≫ μ := rfl

attribute [local simp] mul_eq_mul Grp_Class.inv_eq_inv Grp_Class.comp_inv one_eq_one in
@[reassoc (attr := simp)]
lemma Grp_Class.one_inv : η[G] ≫ ι = η := by simp

end
