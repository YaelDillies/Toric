/-
Copyright (c) 2025 Yaël Dillies, Michał Mrugała, Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Michał Mrugała, Andrew Yang
-/
import Mathlib.CategoryTheory.Monoidal.Cartesian.Mon_

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped Hom Obj

/-! ### `Functor.map` of a fully faithful monoidal functor as a `MulEquiv` -/

namespace CategoryTheory.Functor
variable {C D : Type*} [Category C] [Category D] [CartesianMonoidalCategory C]
  [CartesianMonoidalCategory D] {M X : C} [MonObj M] (F : C ⥤ D) [F.Monoidal]

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

/-! ### Comm monoid objects are internal monoid objects -/

namespace Mon
variable {C : Type*} [Category C] [CartesianMonoidalCategory C] [BraidedCategory C]
  {M N N₁ N₂ : Mon C}

/-- A commutative monoid object is a monoid object in the category of monoid objects. -/
instance [IsCommMonObj M.X] : MonObj M where
  one := .mk η[M.X]
  mul := .mk μ[M.X]

@[simp] lemma hom_η (M : Mon C) [IsCommMonObj M.X] : η[M].hom = η[M.X] := rfl
@[simp] lemma hom_μ (M : Mon C) [IsCommMonObj M.X] : μ[M].hom = μ[M.X] := rfl

namespace Hom
variable [IsCommMonObj N.X]

@[simp] lemma hom_one : (1 : M ⟶ N).hom = 1 := rfl

@[simp] lemma hom_mul (f g : M ⟶ N) : (f * g).hom = f.hom * g.hom := rfl

@[simp] lemma hom_pow (f : M ⟶ N) (n : ℕ) : (f ^ n).hom = f.hom ^ n := by
  induction n <;> simp [pow_succ, *]

end Hom

/-- A commutative monoid object is a commutative monoid object in the category of monoid objects. -/
instance [IsCommMonObj M.X] : IsCommMonObj M where

end Mon

namespace MonObj
variable {C : Type*} [Category C] [CartesianMonoidalCategory C] {M N : C} [MonObj M]
  [MonObj N]

/-- If `M` and `N` are isomorphic as monoid objects, then `X ⟶ M` and `X ⟶ N` are isomorphic
monoids. -/
def homMulEquivRight (e : M ≅ N) [IsMonHom e.hom] (X : C) : (X ⟶ M) ≃* (X ⟶ N) :=
  ((yonedaMon.mapIso <| Mon.mkIso' e).app <| .op X).monCatIsoToMulEquiv

end MonObj
