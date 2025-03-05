import Mathlib.CategoryTheory.Monoidal.Grp_
import Toric.Mathlib.CategoryTheory.ChosenFiniteProducts

/-!
# This is https://github.com/leanprover-community/mathlib4/pull/22168
-/

universe v₁ v₂ u₁ u₂ u
open CategoryTheory Category Limits MonoidalCategory ChosenFiniteProducts Mon_

variable (C : Type u₁) [Category.{v₁} C] [ChosenFiniteProducts.{v₁} C]

section

variable {C}

class Grp_Class (X : C) extends Mon_Class X where
  /-- The inverse in a group object -/
  inv : X ⟶ X
  left_inv' : lift inv (𝟙 X) ≫ mul = toUnit _ ≫ one := by aesop_cat
  right_inv' : lift (𝟙 X) inv ≫ mul = toUnit _ ≫ one := by aesop_cat

namespace Mon_Class

@[inherit_doc] scoped notation "ι" => Grp_Class.inv
@[inherit_doc] scoped notation "ι["M"]" => Grp_Class.inv (X := M)

end Mon_Class

open scoped Mon_Class

namespace Grp_Class

@[reassoc (attr := simp)]
theorem left_inv (X : C) [Grp_Class X] : lift ι (𝟙 X) ≫ μ = toUnit _ ≫ η := left_inv'

@[reassoc (attr := simp)]
theorem right_inv (X : C) [Grp_Class X] : lift (𝟙 X) ι ≫ μ = toUnit _ ≫ η := right_inv'

end Grp_Class

end

namespace Grp_

variable {C}

def mk' (X : C) [Grp_Class X] : Grp_ C where
  __ := Mon_.mk' X
  inv := Grp_Class.inv (X := X)

instance (X : Grp_ C) : Grp_Class X.X where
  inv := X.inv
  left_inv' := X.left_inv
  right_inv' := X.right_inv

theorem lift_left_mul_ext {A : C} {B : Grp_ C} {f g : A ⟶ B.X} (i : A ⟶ B.X)
    (h : lift f i ≫ B.mul = lift g i ≫ B.mul) : f = g := by
  rwa [← eq_lift_inv_right, lift_lift_assoc, lift_comp_inv_right, lift_comp_one_right] at h

@[reassoc (attr := simp)]
theorem inv_comp_inv (A : Grp_ C) : A.inv ≫ A.inv = 𝟙 A.X := by
  apply lift_left_mul_ext A.inv
  rw [right_inv, ← comp_toUnit_assoc A.inv, ← left_inv, comp_lift_assoc, Category.comp_id]

instance (A : Grp_ C) : IsIso A.inv := ⟨A.inv, by simp, by simp⟩

/-- For `inv ≫ inv = 𝟙` see `inv_comp_inv`. -/
@[simp]
theorem inv_inv (A : Grp_ C) : CategoryTheory.inv A.inv = A.inv := by
  rw [eq_comm, ← CategoryTheory.inv_comp_eq_id, IsIso.inv_inv, inv_comp_inv]

@[reassoc]
theorem mul_inv (A : Grp_ C) :
    A.mul ≫ A.inv = (β_ A.X A.X).hom ≫ (A.inv ⊗ A.inv) ≫ A.mul := by
  apply lift_left_mul_ext A.mul
  nth_rw 2 [← Category.comp_id A.mul]
  rw [← comp_lift, Category.assoc, A.left_inv, ← Category.assoc (β_ A.X A.X).hom,
    ← lift_snd_fst, lift_map, lift_lift_assoc]
  nth_rw 2 [← Category.id_comp A.mul]
  rw [← lift_fst_snd, ← lift_lift_assoc (fst A.X A.X ≫ _), lift_comp_inv_left, lift_comp_one_left,
    lift_comp_inv_left, comp_toUnit_assoc]

@[reassoc (attr := simp)]
theorem tensorHom_inv_inv_mul (A : Grp_ C) :
    (A.inv ⊗ A.inv) ≫ A.mul = (β_ A.X A.X).hom ≫ A.mul ≫ A.inv := by
  rw [mul_inv A, SymmetricCategory.symmetry_assoc]

/-- The map `(· * f)`. Note that this is mul "left" because the left argument is varying. -/
@[simps]
def mulRight (A : Grp_ C) (f : 𝟙_ C ⟶ A.X) : A.X ≅ A.X where
  hom := lift (𝟙 _) (toUnit _ ≫ f) ≫ A.mul
  inv := lift (𝟙 _) (toUnit _ ≫ f ≫ A.inv) ≫ A.mul
  hom_inv_id := by simp [comp_lift_assoc, lift_lift_assoc, ← comp_lift]
  inv_hom_id := by simp [comp_lift_assoc, lift_lift_assoc, ← comp_lift]

@[simp]
lemma mulRight_one (A : Grp_ C) : A.mulRight A.one = Iso.refl A.X := by
  ext; simp

open Mon_Class in
@[reassoc]
lemma _root_.IsMon_Hom.inv_hom {X Y : C} [Grp_Class X] [Grp_Class Y] (f : X ⟶ Y) [IsMon_Hom f] :
    ι ≫ f = f ≫ ι :=
  Grp_.inv_hom (A := .mk' X) (B := .mk' Y) (f := ⟨f, IsMon_Hom.one_hom, IsMon_Hom.mul_hom⟩)

lemma _root_.Grp_Class.toMon_Class_injective {X : C} :
    Function.Injective (@Grp_Class.toMon_Class C ‹_› ‹_› X) := by
  intro h₁ h₂ e
  let X₁ : Grp_ C := @Grp_.mk' _ _ _ X h₁
  let X₂ : Grp_ C := @Grp_.mk' _ _ _ X h₂
  suffices X₁.inv = X₂.inv by cases h₁; cases h₂; subst e this; rfl
  apply lift_left_mul_ext (𝟙 _)
  rw [left_inv, show X₁.mul = X₂.mul from congr(($e).mul),
    show X₁.one = X₂.one from congr(($e).one)]
  exact X₂.left_inv.symm

@[ext]
lemma _root_.Grp_Class.ext {X : C} (h₁ h₂ : Grp_Class X)
    (H : h₁.toMon_Class = h₂.toMon_Class) : h₁ = h₂ :=
  Grp_Class.toMon_Class_injective H

end Grp_
