/-
Copyright (c) 2025 Yaël Dillies, Michał Mrugała, Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Michał Mrugała, Andrew Yang
-/
import Mathlib.CategoryTheory.Monoidal.Cartesian.Mon_
import Toric.Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Toric.Mathlib.CategoryTheory.Monoidal.Functor
import Toric.Mathlib.CategoryTheory.Monoidal.CommMon_

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Mon_Class
open scoped Hom Obj

scoped[Hom] attribute [instance] Hom.monoid

universe v₁ v₂ u₁ u₂

attribute [simp] Mon_Class.one_comp Mon_Class.one_comp_assoc Mon_Class.comp_one
  Mon_Class.comp_one_assoc

namespace CategoryTheory.Functor
variable {C D : Type*} [Category C] [Category D] [CartesianMonoidalCategory C]
  [CartesianMonoidalCategory D] {M X : C} [Mon_Class M] (F : C ⥤ D) [F.Monoidal]

lemma map_mul (f g : X ⟶ M) : F.map (f * g) = F.map f * F.map g := by
  simp only [Hom.mul_def, map_comp, obj.μ_def, ← Category.assoc]
  congr 1
  rw [← IsIso.comp_inv_eq]
  ext <;> simp

@[simp]
lemma map_one : F.map (1 : X ⟶ M) = 1 := by
  simp [Hom.one_def]

/-- `Functor.map` as a `MonoidHom`. -/
def mapMonoidHom : (X ⟶ M) →* (F.obj X ⟶ F.obj M) where
  toFun := _
  map_one' := map_one F
  map_mul' := map_mul F

end CategoryTheory.Functor

variable {C : Type*} [Category C] [CartesianMonoidalCategory C] {M N X Y : C} [Mon_Class M]
  [Mon_Class N]

lemma Mon_.one_eq_one (M : Mon_ C) : M.one = 1 := Mon_Class.one_eq_one (M := M.X)

lemma Mon_.mul_eq_mul (M : Mon_ C) : M.mul = fst M.X M.X * snd M.X M.X :=
  Mon_Class.mul_eq_mul (M := M.X)

@[reassoc]
lemma Mon_Class.comp_pow (f : X ⟶ M) (n : ℕ) (h : Y ⟶ X) : h ≫ f ^ n = (h ≫ f) ^ n := by
  induction n <;> simp [pow_succ, Mon_Class.comp_mul, *]

variable [BraidedCategory C]

lemma mul_tensor_mul (f f' : X ⟶ M) (g g' : Y ⟶ N) :
    (f * f') ⊗ (g * g') = (f ⊗ g) * (f' ⊗ g') := by
  simp [Hom.mul_def, Hom.one_def]

lemma one_tensor_one : (1 : X ⟶ M) ⊗ (1 : Y ⟶ N) = 1 := by
  simp only [Hom.one_def, tensor_comp, tensorObj.one_def, ← Category.assoc]
  congr 1
  rw [Iso.eq_comp_inv]
  exact toUnit_unique _ _

attribute [local simp]  one_eq_one

instance : IsMon_Hom (fst M N) where
instance : IsMon_Hom (snd M N) where

/-- If `M` is a commutative monoid object, then `Hom(X, M)` has a commutative monoid structure. -/
abbrev Hom.commMonoid [IsCommMon M] : CommMonoid (X ⟶ M) where
  mul_comm f g := by
    show lift _ _ ≫ _ = lift _ _ ≫ _
    conv_lhs => rw [← IsCommMon.mul_comm]
    rw [← Category.assoc]
    congr 1
    ext <;> simp

scoped[Hom] attribute [instance] Hom.commMonoid

attribute [local simp] mul_eq_mul comp_mul mul_comp one_eq_one Mon_.one_eq_one Mon_.mul_eq_mul

namespace Mon_
variable {M N N₁ N₂ : Mon_ C}

instance instCartesianMonoidalCategory : CartesianMonoidalCategory (Mon_ C) where
  isTerminalTensorUnit :=
    .ofUniqueHom (fun M ↦ .mk (toUnit _) (toUnit_unique ..))
      fun M f ↦ by ext; exact toUnit_unique ..
  fst M N := .mk (fst M.X N.X)
  snd M N := .mk (snd M.X N.X)
  tensorProductIsBinaryProduct M N :=
    BinaryFan.IsLimit.mk _ (fun {T} f g ↦ .mk (lift f.hom g.hom)) (by aesop_cat) (by aesop_cat)
      (by aesop_cat)
  fst_def M N := by ext; simp [fst_def]; congr
  snd_def M N := by ext; simp [snd_def]; congr

@[simp] lemma lift_hom (f : M ⟶ N₁) (g : M ⟶ N₂) : (lift f g).hom = lift f.hom g.hom := rfl
@[simp] lemma fst_hom (M N : Mon_ C) : (fst M N).hom = fst M.X N.X := rfl
@[simp] lemma snd_hom (M N : Mon_ C) : (snd M N).hom = snd M.X N.X := rfl

@[simp] lemma mul_comm [IsCommMon M.X] : (β_ _ _).hom ≫ M.mul = M.mul := IsCommMon.mul_comm _

/-- A commutative monoid object is a monoid object in the category of monoid objects. -/
instance [IsCommMon M.X] : Mon_Class M where
  one :=
    .mk M.one (by simp [Mon_.one_eq_one]) (by simp [toUnit_unique (ρ_ (𝟙_ C)).hom (λ_ (𝟙_ C)).hom])
  mul := .mk M.mul (by simp [toUnit_unique (ρ_ (𝟙_ C)).hom (λ_ (𝟙_ C)).hom]) <| by
    simp only [monMonoidalStruct_tensorObj_X, tensorObj_mul, tensorμ, Category.assoc,
      tensorHom_def'_assoc, ← associator_inv_naturality_right_assoc,
      (Iso.inv_comp_eq _).mpr M.mul_assoc, ← MonoidalCategory.whiskerLeft_comp_assoc,
      ← M.mul_assoc, ← comp_whiskerRight_assoc]
    simp only [mul_comm, mul_assoc, Iso.inv_hom_id_assoc, MonoidalCategory.whiskerLeft_comp,
      Category.assoc, tensor_whiskerLeft]
  one_mul' := by ext; simp [leftUnitor_hom]
  mul_one' := by ext; simp [rightUnitor_hom]
  mul_assoc' := by ext; simp [_root_.mul_assoc]

@[simp] lemma hom_η (M : Mon_ C) [IsCommMon M.X] : η[M].hom = η[M.X] := rfl
@[simp] lemma hom_μ (M : Mon_ C) [IsCommMon M.X] : μ[M].hom = μ[M.X] := rfl

namespace Hom
variable [IsCommMon N.X]

@[simp] lemma hom_one : (1 : M ⟶ N).hom = 1 := rfl

@[simp] lemma hom_mul (f g : M ⟶ N) : (f * g).hom = f.hom * g.hom := rfl

@[simp] lemma hom_pow (f : M ⟶ N) (n : ℕ) : (f ^ n).hom = f.hom ^ n := by
  induction n <;> simp [pow_succ, *]

end Hom

/-- A commutative monoid object is a commutative monoid object in the category of monoid objects. -/
instance [IsCommMon M.X] : IsCommMon M where mul_comm' := by ext; simp [_root_.mul_comm]

end Mon_
