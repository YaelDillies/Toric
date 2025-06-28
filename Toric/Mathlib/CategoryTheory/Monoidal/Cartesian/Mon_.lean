/-
Copyright (c) 2025 Yaël Dillies, Michał Mrugała, Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Michał Mrugała, Andrew Yang
-/
import Mathlib.CategoryTheory.Monoidal.Cartesian.Mon_
import Toric.Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Toric.Mathlib.CategoryTheory.Monoidal.Mon_
import Toric.Mathlib.CategoryTheory.Monoidal.Functor
import Toric.Mathlib.CategoryTheory.Monoidal.CommMon_

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Mon_Class
open scoped Hom Obj

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
lemma map_one : F.map (1 : X ⟶ M) = 1 := by simp [Hom.one_def]

/-- `Functor.map` of a monoidal functor as a `MonoidHom`. -/
@[simps]
def homMonoidHom : (X ⟶ M) →* (F.obj X ⟶ F.obj M) where
  toFun := F.map
  map_one' := map_one F
  map_mul' := map_mul F

/-- `Functor.map` of a fully faithful monoidal functor as a `MulEquiv`. -/
@[simps!]
def FullyFaithful.homMulEquiv (hF : F.FullyFaithful) : (X ⟶ M) ≃* (F.obj X ⟶ F.obj M) where
  __ := hF.homEquiv
  __ := F.homMonoidHom

end CategoryTheory.Functor

namespace Mon_Class
variable {C : Type*} [Category C] [CartesianMonoidalCategory C] {M N O X Y : C} [Mon_Class M]
  [Mon_Class N] [Mon_Class O]

instance : IsMon_Hom (toUnit M) where
instance : IsMon_Hom η[M] where
  mul_hom := by simp [toUnit_unique (ρ_ (𝟙_ C)).hom (λ_ (𝟙_ C)).hom]

variable [BraidedCategory C]

attribute [local simp] tensorObj.one_def tensorObj.mul_def in
attribute [-simp] IsMon_Hom.one_hom IsMon_Hom.one_hom_assoc IsMon_Hom.mul_hom
  IsMon_Hom.mul_hom_assoc in
instance : IsMon_Hom (fst M N) where

attribute [local simp] tensorObj.one_def tensorObj.mul_def in
attribute [-simp] IsMon_Hom.one_hom IsMon_Hom.one_hom_assoc IsMon_Hom.mul_hom
  IsMon_Hom.mul_hom_assoc in
instance : IsMon_Hom (snd M N) where

lemma mul_tensorHom_mul (f f' : X ⟶ M) (g g' : Y ⟶ N) :
    (f * f') ⊗ₘ (g * g') = (f ⊗ₘ g) * (f' ⊗ₘ g') := by
  simp [Hom.mul_def, Hom.one_def, tensorObj.mul_def]

lemma one_tensorHom_one : (1 : X ⟶ M) ⊗ₘ (1 : Y ⟶ N) = 1 := by
  simp only [Hom.one_def, tensor_comp, tensorObj.one_def, ← Category.assoc]
  congr 1
  rw [Iso.eq_comp_inv]
  exact toUnit_unique _ _

attribute [local simp] tensorObj.one_def tensorObj.mul_def in
attribute [-simp] IsMon_Hom.one_hom IsMon_Hom.one_hom_assoc IsMon_Hom.mul_hom
  IsMon_Hom.mul_hom_assoc in
instance {f : M ⟶ N} {g : M ⟶ O} [IsMon_Hom f] [IsMon_Hom g] : IsMon_Hom (lift f g) where
  one_hom := by ext <;> simp [IsMon_Hom.one_hom f, IsMon_Hom.one_hom g]
  mul_hom := by ext <;> simp [← tensor_comp_assoc, IsMon_Hom.mul_hom f, IsMon_Hom.mul_hom g]

attribute [local simp] tensorObj.one_def tensorObj.mul_def in
attribute [-simp] IsMon_Hom.one_hom IsMon_Hom.one_hom_assoc IsMon_Hom.mul_hom
  IsMon_Hom.mul_hom_assoc in
instance [IsCommMon M] : IsMon_Hom μ[M] where
  one_hom := by simp [toUnit_unique (ρ_ (𝟙_ C)).hom (λ_ (𝟙_ C)).hom]

end Mon_Class

attribute [local simp] mul_eq_mul comp_mul mul_comp one_eq_one

namespace Mon_
variable {C : Type*} [Category C] [CartesianMonoidalCategory C] [BraidedCategory C]
  {M N N₁ N₂ : Mon_ C}

instance instCartesianMonoidalCategory : CartesianMonoidalCategory (Mon_ C) where
  isTerminalTensorUnit :=
    .ofUniqueHom (fun M ↦ .mk (toUnit _)) fun M f ↦ by ext; exact toUnit_unique ..
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

/-- A commutative monoid object is a monoid object in the category of monoid objects. -/
instance [IsCommMon M.X] : Mon_Class M where
  one := .mk η[M.X]
  mul := .mk μ[M.X]
  one_mul := by ext; simp [leftUnitor_hom]
  mul_one := by ext; simp [rightUnitor_hom]
  mul_assoc := by ext; simp [_root_.mul_assoc]

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
instance [IsCommMon M.X] : IsCommMon M where mul_comm := by ext; simp [_root_.mul_comm]

end Mon_

namespace Mon_Class
variable {C : Type*} [Category C] [CartesianMonoidalCategory C] {M N : C} [Mon_Class M]
  [Mon_Class N]

/-- If `M` and `N` are isomorphic as monoid objects, then `X ⟶ M` and `X ⟶ N` are isomorphic
monoids. -/
def homMulEquivRight (e : M ≅ N) [IsMon_Hom e.hom] (X : C) : (X ⟶ M) ≃* (X ⟶ N) :=
  ((yonedaMon.mapIso <| Mon_.mkIso'' e).app <| .op X).monCatIsoToMulEquiv

end Mon_Class
