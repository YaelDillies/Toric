/-
Copyright (c) 2025 Yaël Dillies, Michał Mrugała, Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Michał Mrugała, Andrew Yang
-/
import Mathlib.CategoryTheory.Monoidal.Cartesian.Mon_

open CategoryTheory Limits CartesianMonoidalCategory Mon_Class

universe v₁ v₂ u₁ u₂

section

attribute [local instance] Hom.monoid

attribute [simp] Mon_Class.one_comp Mon_Class.one_comp_assoc Mon_Class.comp_one
  Mon_Class.comp_one_assoc

variable {C : Type*} [Category C] [CartesianMonoidalCategory C] {M N X Y : C} [Mon_Class M]
  [Mon_Class N]

lemma Mon_.one_eq_one {M : Mon_ C} : M.one = 1 := Mon_Class.one_eq_one (M := M.X)

lemma Mon_.mul_eq_mul {M : Mon_ C} : M.mul = (fst _ _ * snd _ _) := Mon_Class.mul_eq_mul (M := M.X)

@[reassoc]
lemma Mon_Class.comp_pow (f : X ⟶ M) (n : ℕ) (h : Y ⟶ X) : h ≫ f ^ n = (h ≫ f) ^ n := by
  induction' n with n hn
  · simp
  simp only [pow_succ, Mon_Class.comp_mul, hn]

variable [BraidedCategory C]

instance Hom.instCommMonoid [IsCommMon M] : CommMonoid (X ⟶ M) where
  mul_comm f g := by
    show lift _ _ ≫ _ = lift _ _ ≫ _
    conv_lhs => rw [← IsCommMon.mul_comm]
    rw [← Category.assoc]
    congr 1
    ext <;> simp

end

namespace Mon_.Hom

variable {C : Type*} [Category C] [CartesianMonoidalCategory C] {M N : Mon_ C}

attribute [local instance] Hom.monoid

instance instOne : One (M ⟶ N) where
  one.hom := 1
  one.one_hom := by simp [one_eq_one]
  one.mul_hom := by simp [mul_eq_mul, Mon_Class.comp_mul]

lemma hom_one : (1 : (M ⟶ N)).hom = 1 := rfl

variable [BraidedCategory C] [IsCommMon N.X]

instance instMul : Mul (M ⟶ N) where
  mul f g := {
    hom := f.hom * g.hom
    one_hom := by simp [Mon_.one_eq_one, Mon_Class.comp_mul, Mon_Class.one_comp]
    mul_hom := by simp [mul_eq_mul, comp_mul, mul_comp, mul_mul_mul_comm]
  }

@[simp]
lemma hom_mul (f g : M ⟶ N) : (f * g).hom = f.hom * g.hom := rfl

instance instPow : Pow (M ⟶ N) ℕ where
  pow f n := {
    hom := f.hom ^ n
    one_hom := by simp [Mon_.one_eq_one, Mon_Class.one_comp, Mon_Class.comp_pow]
    mul_hom := by
      simp [mul_eq_mul, Mon_Class.comp_mul, Mon_Class.mul_comp, Mon_Class.comp_pow, mul_pow]
  }

@[simp] lemma hom_pow (f : M ⟶ N) (n : ℕ) : (f ^ n).hom = f.hom ^ n := rfl

instance : CommMonoid (M ⟶ N) :=
  Function.Injective.commMonoid hom (fun _ _ ↦ ext) hom_one hom_mul hom_pow

end Mon_.Hom
