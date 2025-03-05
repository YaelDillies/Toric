/-
Copyright (c) 2025 Yaël Dillies, Michał Mrugała, Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Michał Mrugała, Andrew Yang
-/
import Mathlib.CategoryTheory.Monoidal.Grp_
import Toric.Mathlib.CategoryTheory.Monoidal.Grp_
import Mathlib.CategoryTheory.Monoidal.Yoneda
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Toric.GroupScheme.YonedaGrp
import Toric.Mathlib.CategoryTheory.Monoidal.CommMon_

open CategoryTheory Mon_Class MonoidalCategory ChosenFiniteProducts
section

variable {C : Type*} [Category C] [MonoidalCategory C] {M N : Mon_ C}

instance {M N : Mon_ C} (f : M ⟶ N) : IsMon_Hom f.hom := ⟨f.2, f.3⟩

def Mon_.homMk {M N : C} [Mon_Class M] [Mon_Class N] (f : M ⟶ N) [IsMon_Hom f] :
    Mon_.mk' M ⟶ Mon_.mk' N := ⟨f, IsMon_Hom.one_hom, IsMon_Hom.mul_hom⟩

end
section

attribute [local instance] monoidOfMon_Class

variable {C : Type*} [Category C] [ChosenFiniteProducts C] {M N : Mon_ C}  [IsCommMon N.X]

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
    (f * g) ≫ h = f ≫ h * g ≫ h := ((yonedaMon.map (Mon_.homMk h)).app (.op M)).hom.map_mul f g

@[reassoc (attr := simp)]
lemma Mon_Class.one_comp {M N O : C} (h : N ⟶ O) [Mon_Class N] [Mon_Class O]
    [IsMon_Hom h] : (1 : M ⟶ N) ≫ h = 1 := ((yonedaMon.map (Mon_.homMk h)).app (.op M)).hom.map_one

@[reassoc (attr := simp)]
lemma Mon_Class.comp_one {M N O : C} (h : M ⟶ N) [Mon_Class O] :
    h ≫ (1 : N ⟶ O) = 1 :=  ((yonedaMon.obj (.mk' O)).map (h.op)).hom.map_one

instance Hom.instCommMonoid {M N : C} [Mon_Class N] [IsCommMon N] : CommMonoid (M ⟶ N) where
  mul_comm f g := by
    show lift _ _ ≫ _ = lift _ _ ≫ _
    conv_lhs => rw [← IsCommMon.mul_comm N]
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

namespace Mon_.Hom

variable {C : Type*} [Category C] [ChosenFiniteProducts C] {M N : Mon_ C}

attribute [local instance] monoidOfMon_Class

instance instOne : One (M ⟶ N) where
  one := {
    hom := 1
    one_hom := by simp [Mon_.one_eq_one]
    mul_hom := by simp [Mon_.mul_eq_mul, Mon_Class.comp_mul]
  }

lemma hom_one : (1 : (M ⟶ N)).hom = 1 := rfl

variable [IsCommMon N.X]

instance instMul : Mul (M ⟶ N) where
  mul f g :=
  { hom := f.hom * g.hom
    one_hom := by simp [Mon_.one_eq_one, Mon_Class.comp_mul, Mon_Class.one_comp]
    mul_hom := by
      simp [mul_eq_mul, comp_mul, mul_comp, mul_mul_mul_comm] }

@[simp]
lemma hom_mul (f g : M ⟶ N) : (f * g).hom = f.hom * g.hom := rfl

instance instPow : Pow (M ⟶ N) ℕ where
  pow f n :=
  { hom := f.hom ^ n
    one_hom := by simp [Mon_.one_eq_one, Mon_Class.one_comp, Mon_Class.comp_pow]
    mul_hom := by
      simp [Mon_.mul_eq_mul, Mon_Class.comp_mul, Mon_Class.mul_comp, Mon_Class.comp_pow, mul_pow]
  }

@[simp]
lemma hom_pow (f : M ⟶ N) (n : ℕ) : (f ^ n).hom = f.hom ^ n := rfl

instance : CommMonoid (M ⟶ N) :=
  Function.Injective.commMonoid hom (fun _ _ ↦ ext) hom_one hom_mul hom_pow

end  Mon_.Hom

section

open ChosenFiniteProducts MonoidalCategory

variable {C : Type*} [Category C] [ChosenFiniteProducts C] {G H : Grp_ C}

attribute [local instance] groupOfGrp_Class

def Grp_.homMk {G H : C} [Grp_Class G] [Grp_Class H] (f : G ⟶ H) [IsMon_Hom f] :
    Grp_.mk' G ⟶ Grp_.mk' H := ⟨f, IsMon_Hom.one_hom, IsMon_Hom.mul_hom⟩

@[reassoc]
lemma Grp_Class.comp_inv {G H K : C} (f : G ⟶ H) (h : K ⟶ G) [Grp_Class H] :
    h ≫ f⁻¹ = (h ≫ f)⁻¹ := ((yonedaGrp.obj (.mk' H)).map (h.op)).hom.map_inv f

@[reassoc]
lemma Grp_Class.comp_div {G H K : C} (f g : G ⟶ H) (h : K ⟶ G) [Grp_Class H] :
    h ≫ (f / g) = h ≫ f / h ≫ g :=
  (((yonedaGrp.obj (.mk' H)).map (h.op)).hom.map_div f g)

@[reassoc]
lemma Grp_Class.div_comp {G H K : C} (f g : G ⟶ H) (h : H ⟶ K) [Grp_Class H] [Grp_Class K]
    [IsMon_Hom h] : (f / g) ≫ h =  (f ≫ h) / (g ≫ h) :=
    (((yonedaGrp.map (Grp_.homMk h)).app (.op G)).hom.map_div f g)

lemma Grp_Class.inv_eq_comp_inv {G H : C} (f : G ⟶ H) [Grp_Class H] : f ≫ ι = f⁻¹ := rfl

lemma Grp_Class.mul_eq_comp_mul {G H : C} {f g : G ⟶ H} [Grp_Class H] : f * g = lift f g ≫ μ := rfl

lemma Grp_Class.mul_inv_rev {G : C} [Grp_Class G] :
    μ ≫ ι = ((ι : G ⟶ G) ⊗ ι) ≫ (β_ _ _).hom ≫ μ := by
  calc
    _ = ((fst G G) * (snd G G)) ≫ ι := by rw [mul_eq_mul]
    _ = (snd G G)⁻¹ * (fst G G)⁻¹ := by rw [Grp_Class.inv_eq_comp_inv]; simp
    _ = lift (snd G G ≫ ι) (fst G G ≫ ι) ≫ μ := rfl
    _ = lift (fst G G ≫ ι) (snd G G ≫ ι) ≫ (β_ G G).hom ≫ μ := by simp
    _ = ((ι : G ⟶ G) ⊗ ι) ≫ (β_ _ _).hom ≫ μ := by simp

instance Hom.instCommGroup {G H : C} [Grp_Class H] [IsCommMon H] :
    CommGroup (G ⟶ H) where
  __ := Hom.instCommMonoid
  inv_mul_cancel f := by simp

@[reassoc]
lemma Grp_Class.comp_zpow {G H K : C} [Grp_Class H] (f : G ⟶ H) (h : K ⟶ G) :
    ∀ n : ℤ, h ≫ f ^ n = (h ≫ f) ^ n
  | (n : ℕ) => by simp [comp_pow]
  | .negSucc n => by simp [comp_pow, comp_inv]

namespace Grp_.Hom

instance instOne : One (G ⟶ H) := inferInstanceAs <| One (G.toMon_ ⟶ H.toMon_)

lemma hom_one : (1 : (G ⟶ H)).hom = 1 := rfl

variable [IsCommMon H.X]

instance instMul : Mul (G ⟶ H) := inferInstanceAs <| Mul (G.toMon_ ⟶ H.toMon_)

@[simp]
lemma hom_mul (f g : G ⟶ H) : (f * g).hom = f.hom * g.hom := rfl

instance instPow : Pow (G ⟶ H) ℕ := inferInstanceAs <| Pow (G.toMon_ ⟶ H.toMon_) ℕ

@[simp]
lemma hom_pow (f : G ⟶ H) (n : ℕ) : (f ^ n).hom = f.hom ^ n := rfl

instance {G : C} [Grp_Class G] [IsCommMon G] : IsMon_Hom (ι : G ⟶ G) where
  one_hom := by simp only [one_eq_one]; exact inv_one
  mul_hom := by
    simp [Grp_Class.mul_inv_rev]

instance {f : G ⟶ H} [IsCommMon H.X] : IsMon_Hom f.hom⁻¹ where
  one_hom := by
    change _ ≫ _ ≫ _ = _
    simp [Mon_Class.one_eq_one, one_comp]
  mul_hom := by
    simp [← Grp_Class.inv_eq_comp_inv]

instance instInv : Inv (G ⟶ H) where
  inv f := {
    hom := f.hom⁻¹
    one_hom := by simp only [Mon_.one_eq_one, one_comp_assoc]; rw [one_comp]
    mul_hom := by simp [Mon_.mul_eq_mul, Mon_Class.comp_mul, Mon_Class.mul_comp]
  }

@[simp]
lemma hom_inv (f : G ⟶ H) : (f⁻¹).hom = f.hom⁻¹ := rfl

instance instDiv : Div (G ⟶ H) where
  div f g :=
  { hom := f.hom / g.hom
    one_hom := by simp [Mon_.one_eq_one, Grp_Class.comp_div, Mon_Class.one_comp]
    mul_hom := by
      simp [Mon_.mul_eq_mul, Grp_Class.comp_div, Mon_Class.comp_mul, Mon_Class.mul_comp,
          mul_div_mul_comm] }

@[simp]
lemma hom_div (f g : G ⟶ H) : (f / g).hom = f.hom / g.hom := rfl

instance instPowInt : Pow (G ⟶ H) ℤ where
  pow f i := {
    hom := f.hom ^ i
    one_hom := by simp [Mon_.one_eq_one, Mon_Class.one_comp, Grp_Class.comp_zpow]
    mul_hom := by
      simp [Mon_.mul_eq_mul, Mon_Class.comp_mul, Mon_Class.mul_comp, Grp_Class.comp_zpow, mul_zpow]
  }

@[simp]
lemma hom_zpow (f : G ⟶ H) (n : ℤ) : (f ^ n).hom = f.hom ^ n := rfl

instance instCommGroup : CommGroup (G ⟶ H) :=
  Function.Injective.commGroup Mon_.Hom.hom (fun _ _ ↦ Mon_.Hom.ext)
    hom_one hom_mul hom_inv hom_div hom_pow hom_zpow

end Grp_.Hom
end
