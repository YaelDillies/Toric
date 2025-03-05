/-
Copyright (c) 2025 Yaël Dillies, Michał Mrugała, Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Michał Mrugała, Andrew Yang
-/
import Mathlib.CategoryTheory.Monoidal.Grp_
import Mathlib.CategoryTheory.Monoidal.Yoneda
import Mathlib.Combinatorics.Quiver.ReflQuiver

open CategoryTheory Mon_Class MonoidalCategory ChosenFiniteProducts

section
variable {C : Type*} [Category C] [MonoidalCategory C] [BraidedCategory C]

class CommMon_Class (X : C) [Mon_Class X] where
  mul_comm' : (β_ X X).hom ≫ μ = μ := by aesop_cat

namespace CommMon_Class

@[reassoc (attr := simp)]
theorem mul_comm (X : C) [Mon_Class X] [CommMon_Class X] : (β_ X X).hom ≫ μ = μ := mul_comm'

end CommMon_Class

end


section

variable {C : Type*} [Category C] [MonoidalCategory C] {M N : Mon_ C}

instance {M N : Mon_ C} (f : M ⟶ N) : IsMon_Hom f.hom := ⟨f.2, f.3⟩

def Mon_.homMk {M N : C} [Mon_Class M] [Mon_Class N] (f : M ⟶ N) [IsMon_Hom f] :
    Mon_.mk' M ⟶ Mon_.mk' N := ⟨f, IsMon_Hom.one_hom, IsMon_Hom.mul_hom⟩

end
section

attribute [local instance] monoidOfMon_Class

variable {C : Type*} [Category C] [ChosenFiniteProducts C] {M N : Mon_ C}  [CommMon_Class N.X]

@[reassoc]
lemma Mon_Class.comp_mul {M N O : C} (f g : M ⟶ N) (h : O ⟶ M) [Mon_Class N] :
    h ≫ (f * g) = h ≫ f * h ≫ g :=
  (((yonedaMon.obj (.mk' N)).map (h.op)).hom.map_mul f g)

lemma Mon_Class.one_eq_one {M : C} [Mon_Class M] :
    η = (1 : _ ⟶ M) := by
  show _ = _ ≫ _
  rw [toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]

lemma Mon_Class.mul_eq_mul {M : C} [Mon_Class M] :
    μ = fst M M * snd _ _ := by
  show _ = _ ≫ _
  rw [lift_fst_snd, Category.id_comp]

lemma Mon_.one_eq_one {M : Mon_ C} :
    M.one = 1 :=
  Mon_Class.one_eq_one (M := M.X)

lemma Mon_.mul_eq_mul {M : Mon_ C} :
    M.mul = (fst _ _ * snd _ _) :=
  Mon_Class.mul_eq_mul (M := M.X)

@[reassoc]
lemma Mon_Class.mul_comp {M N O : C} (f g : M ⟶ N) (h : N ⟶ O) [Mon_Class N] [Mon_Class O]
    [IsMon_Hom h] :
    (f * g) ≫ h = (f ≫ h) * g ≫ h :=
  (((yonedaMon.map (Mon_.homMk h)).app (.op M)).hom.map_mul f g)

@[reassoc (attr := simp)]
lemma Mon_Class.one_comp {M N O : C} (h : N ⟶ O) [Mon_Class N] [Mon_Class O]
    [IsMon_Hom h] : (1 : M ⟶ N) ≫ h = 1 :=
  ((yonedaMon.map (Mon_.homMk h)).app (.op M)).hom.map_one

@[reassoc (attr := simp)]
lemma Mon_Class.comp_one {M N O : C} (h : M ⟶ N) [Mon_Class O] :
    h ≫ (1 : N ⟶ O) = 1 :=
  (((yonedaMon.obj (.mk' O)).map (h.op)).hom.map_one)

instance {M N : C} [Mon_Class N] [CommMon_Class N] : CommMonoid (M ⟶ N) where
  mul_comm f g := by
    show lift _ _ ≫ _ = lift _ _ ≫ _
    conv_lhs => rw [← CommMon_Class.mul_comm N]
    rw [← Category.assoc]
    congr 1
    ext <;> simp

@[reassoc]
lemma Mon_Class.comp_pow {M N O : C} (f : M ⟶ N) (n : ℕ) (h : O ⟶ M) [Mon_Class N] :
    h ≫ f ^ n = (h ≫ f) ^ n := by
  induction' n with n hn
  · simp
  simp only [pow_succ, Mon_Class.comp_mul, hn]

end

namespace Mon_

variable {C : Type*} [Category C] [ChosenFiniteProducts C] {M N : Mon_ C}

attribute [local instance] monoidOfMon_Class

instance Hom.instOne : One (M ⟶ N) where
  one := {
    hom := 1
    one_hom := by simp [Mon_.one_eq_one]
    mul_hom := by simp [Mon_.mul_eq_mul, Mon_Class.comp_mul]
  }

lemma Hom.one_mul : (1 : (M ⟶ N)) = 1 := rfl

variable [CommMon_Class N.X]

instance Hom.instMul : Mul (M ⟶ N) where
  mul f g :=
  { hom := f.hom * g.hom
    one_hom := by simp [Mon_.one_eq_one, Mon_Class.comp_mul, Mon_Class.one_comp]
    mul_hom := by simp [Mon_.mul_eq_mul, Mon_Class.comp_mul, Mon_Class.mul_comp, mul_mul_mul_comm] }

@[simp]
lemma Hom.hom_mul (f g : M ⟶ N) : (f * g).hom = f.hom * g.hom := rfl

instance Hom.instPow : Pow (M ⟶ N) ℕ where
  pow f n :=
  { hom := f.hom ^ n
    one_hom := by simp [Mon_.one_eq_one, Mon_Class.one_comp, Mon_Class.comp_pow]
    mul_hom := by
      simp [Mon_.mul_eq_mul, Mon_Class.comp_mul, Mon_Class.mul_comp, mul_mul_mul_comm,
      Mon_Class.comp_pow, mul_pow]
  }

@[simp]
lemma Hom.hom_pow (f : M ⟶ N) (n : ℕ) : (f ^ n).hom = f.hom ^ n := rfl

instance : CommMonoid (M ⟶ N) :=
  Function.Injective.commMonoid Hom.hom (fun _ _ ↦ Hom.ext) rfl (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)

end  Mon_

namespace Grp_

open ChosenFiniteProducts MonoidalCategory

variable {C : Type*} [Category C] [ChosenFiniteProducts C] {G H : Grp_ C}

instance Hom.instOne : One (G ⟶ H) := inferInstanceAs <| One (G.toMon_ ⟶ H.toMon_)

lemma Hom.one_mul : (1 : (G ⟶ H)) = 1 := rfl

variable [CommMon_Class H.X]

instance Hom.instMul : Mul (G ⟶ H) := inferInstanceAs <| Mul (G.toMon_ ⟶ H.toMon_)

@[simp]
lemma Hom.hom_mul (f g : G ⟶ H) : (f * g).hom = f.hom * g.hom := rfl

instance Hom.instPow : Pow (G ⟶ H) ℕ := inferInstanceAs <| Pow (G.toMon_ ⟶ H.toMon_) ℕ

@[simp]
lemma Hom.hom_pow (f : G ⟶ H) (n : ℕ) : (f ^ n).hom = f.hom ^ n := rfl

instance : CommGroup (G ⟶ H) := sorry
  -- Function.Injective.commGroup Mon_.Hom.hom (fun _ _ ↦ Mon_.Hom.ext) rfl (fun _ _ ↦ rfl)
  --   (fun _ _ ↦ rfl) _

end Grp_
