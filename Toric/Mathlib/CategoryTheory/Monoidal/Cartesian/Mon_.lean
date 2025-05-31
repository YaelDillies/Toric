/-
Copyright (c) 2025 Yaël Dillies, Michał Mrugała, Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Michał Mrugała, Andrew Yang
-/
import Mathlib.CategoryTheory.Monoidal.Cartesian.Mon_
import Toric.Mathlib.CategoryTheory.Monoidal.Functor
import Toric.Mathlib.CategoryTheory.Monoidal.Mon_
import Toric.Mathlib.CategoryTheory.Monoidal.CommMon_
import Toric.Mathlib.CategoryTheory.Monoidal.Cartesian.Basic

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Mon_Class
open scoped Hom Obj

scoped[Hom] attribute [instance] Hom.monoid

universe v₁ v₂ u₁ u₂

section

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

variable [BraidedCategory C] [BraidedCategory D]

instance [F.LaxBraided] : F.mapMon.LaxBraided where
  braided M N := by ext; exact LaxBraided.braided ..

open OplaxMonoidal

instance [F.Braided] : F.mapMon.Braided where
  η' := .mk («η» F)
  δ' M N := .mk  (δ F M.X N.X) sorry sorry

end CategoryTheory.Functor

variable {C : Type*} [Category C] [CartesianMonoidalCategory C] {M N X Y : C}
  [Mon_Class M] [Mon_Class N]

lemma Mon_.one_eq_one (M : Mon_ C) : M.one = 1 := Mon_Class.one_eq_one (M := M.X)

lemma Mon_.mul_eq_mul (M : Mon_ C) : M.mul = fst M.X M.X * snd M.X M.X :=
  Mon_Class.mul_eq_mul (M := M.X)

@[reassoc]
lemma Mon_Class.comp_pow (f : X ⟶ M) (n : ℕ) (h : Y ⟶ X) : h ≫ f ^ n = (h ≫ f) ^ n := by
  induction n <;> simp [pow_succ, Mon_Class.comp_mul, *]

variable [BraidedCategory C]

/-- If `M` is a commutative monoid object, then `Hom(X, M)` has a commutative monoid structure. -/
abbrev Hom.commMonoid [IsCommMon M] : CommMonoid (X ⟶ M) where
  mul_comm f g := by
    show lift _ _ ≫ _ = lift _ _ ≫ _
    conv_lhs => rw [← IsCommMon.mul_comm]
    rw [← Category.assoc]
    congr 1
    ext <;> simp

scoped[Hom] attribute [instance] Hom.commMonoid

end

namespace Mon_
variable {C : Type*} [Category C] [CartesianMonoidalCategory C] [BraidedCategory C]
  {M N N₁ N₂ : Mon_ C}

instance instCartesianMonoidalCategory : CartesianMonoidalCategory (Mon_ C) where
  isTerminalTensorUnit :=
    .ofUniqueHom (fun M ↦ .mk (toUnit _) (toUnit_unique ..))
      fun M f ↦ by ext; exact toUnit_unique ..
  fst M N := .mk (fst M.X N.X) (by simp [toUnit_unique _ (𝟙 _)])
  snd M N := .mk (snd M.X N.X) (by simp [toUnit_unique _ (𝟙 _)])
  tensorProductIsBinaryProduct M N :=
    BinaryFan.IsLimit.mk _ (fun {T} f g ↦ .mk (lift f.hom g.hom)
      (by simp; ext <;> simp [toUnit_unique _ (𝟙 _)])
      (by simp; ext <;> simp [toUnit_unique _ (𝟙 _), ← tensor_comp_assoc]))
      (by aesop_cat) (by aesop_cat) (by aesop_cat)
  fst_def M N := by ext; simp [fst_def]; congr
  snd_def M N := by ext; simp [snd_def]; congr

@[simp] lemma lift_hom (f : M ⟶ N₁) (g : M ⟶ N₂) : (lift f g).hom = lift f.hom g.hom := rfl
@[simp] lemma fst_hom (M N : Mon_ C) : (fst M N).hom = fst M.X N.X := rfl
@[simp] lemma snd_hom (M N : Mon_ C) : (snd M N).hom = snd M.X N.X := rfl

/-- A commutative monoid object is a monoid object in the category of monoid objects. -/
instance [IsCommMon M.X] : Mon_Class M where
  one :=
    .mk M.one (by simp [Mon_.one_eq_one]) (by simp [toUnit_unique (ρ_ (𝟙_ C)).hom (λ_ (𝟙_ C)).hom])
  mul := .mk M.mul (by simp [toUnit_unique (ρ_ (𝟙_ C)).hom (λ_ (𝟙_ C)).hom]) <| by
    simp
    sorry
  one_mul' := by ext; simp
  mul_one' := by ext; simp
  mul_assoc' := by ext; simp

@[simp] lemma hom_η (M : Mon_ C) [IsCommMon M.X] : η[M].hom = η[M.X] := rfl
@[simp] lemma hom_μ (M : Mon_ C) [IsCommMon M.X] : μ[M].hom = μ[M.X] := rfl

/-- A commutative monoid object is a commutative monoid object in the category of monoid objects. -/
instance [IsCommMon M.X] : IsCommMon M where mul_comm' := by ext; simp

namespace Hom
variable [IsCommMon N.X]

@[simp] lemma hom_one : (1 : M ⟶ N).hom = 1 := rfl

@[simp] lemma hom_mul (f g : M ⟶ N) : (f * g).hom = f.hom * g.hom := rfl

@[simp] lemma hom_pow (f : M ⟶ N) (n : ℕ) : (f ^ n).hom = f.hom ^ n := by
  induction n <;> simp [pow_succ, *]

end Mon_.Hom
