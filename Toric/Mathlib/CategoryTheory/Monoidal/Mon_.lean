/-
Copyright (c) 2025 Yaël Dillies, Michał Mrugała, Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Michał Mrugała, Andrew Yang
-/
import Mathlib.CategoryTheory.Monoidal.Yoneda
import Toric.Mathlib.CategoryTheory.ChosenFiniteProducts.Over

open CategoryTheory ChosenFiniteProducts Mon_Class MonoidalCategory

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

section Yoneda
variable {C : Type*} [Category C] [ChosenFiniteProducts C]

variable {X G : C} [Mon_Class G]

-- TODO (Michał): doc string
def yonedaMonObjMon_ClassOfRepresentableBy :
    ((Over.forget X).op ⋙ yonedaMonObj G ⋙ forget MonCat).RepresentableBy (.mk (snd G X)) where
  homEquiv {Y} := show (Y ⟶ Over.mk (snd G X)) ≃ (Y.left ⟶ G) from {
      toFun f := f.left ≫ fst _ _
      invFun f := Over.homMk (lift f Y.hom)
      left_inv f := by ext; simp; ext <;> simp; simpa using f.w.symm
      right_inv f := by simp
    }
  homEquiv_comp {Y Z} f g := by dsimp; erw [Equiv.coe_fn_mk, Equiv.coe_fn_mk]; simp

variable [Limits.HasPullbacks C]

attribute [local instance] Over.chosenFiniteProducts

noncomputable instance : Mon_Class <| Over.mk <| snd G X :=
  Mon_Class.ofRepresentableBy _ ((Over.forget _).op ⋙ yonedaMonObj G)
      yonedaMonObjMon_ClassOfRepresentableBy

end Yoneda
