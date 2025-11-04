/-
Copyright (c) 2025 Yaël Dillies, Michał Mrugała, Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Michał Mrugała, Andrew Yang
-/
import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp_
import Toric.Mathlib.CategoryTheory.Monoidal.Cartesian.Mon_

open CategoryTheory MonObj MonoidalCategory CartesianMonoidalCategory

/-! ### Internal groups -/

namespace Grp
variable {C : Type*} [Category C] [CartesianMonoidalCategory C] [BraidedCategory C] {G H : Grp C}
  [IsCommMonObj H.X]

-- TODO: Make `Grp.toMon` an abbrev in mathlib.
set_option allowUnsafeReducibility true in
attribute [reducible] Grp.toMon

instance : MonObj H where
  one := η[H.toMon]
  mul := μ[H.toMon]
  one_mul := MonObj.one_mul H.toMon
  mul_one := MonObj.mul_one H.toMon
  mul_assoc := MonObj.mul_assoc H.toMon

variable (H) in
@[simp] lemma hom_one : η[H].hom = η[H.X] := rfl

variable (H) in
@[simp] lemma hom_mul : μ[H].hom = μ[H.X] := rfl

namespace Hom

@[simp] lemma hom_one : (1 : G ⟶ H).hom = 1 := rfl
@[simp] lemma hom_mul (f g : G ⟶ H) : (f * g).hom = f.hom * g.hom := rfl
@[simp] lemma hom_pow (f : G ⟶ H) (n : ℕ) : (f ^ n).hom = f.hom ^ n := Mon.Hom.hom_pow ..

end Hom

attribute [local simp] mul_eq_mul GrpObj.inv_eq_inv comp_mul in
/-- A commutative group object is a group object in the category of group objects. -/
instance : GrpObj H where inv := .mk ι[H.X]

namespace Hom

@[simp] lemma hom_inv (f : G ⟶ H) : f⁻¹.hom = f.hom⁻¹ := rfl
@[simp] lemma hom_div (f g : G ⟶ H) : (f / g).hom = f.hom / g.hom := rfl
@[simp] lemma hom_zpow (f : G ⟶ H) (n : ℤ) : (f ^ n).hom = f.hom ^ n := by cases n <;> simp

end Hom

attribute [local simp] mul_eq_mul comp_mul mul_comm mul_div_mul_comm in
/-- A commutative group object is a commutative group object in the category of group objects. -/
instance : IsCommMonObj H where

instance [IsCommMonObj G.X] (f : G ⟶ H) : IsMonHom f where

end Grp
