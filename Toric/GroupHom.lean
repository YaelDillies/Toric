/-
Copyright (c) 2025 Yaël Dillies, Michał Mrugała. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Michał Mrugała
-/

import Mathlib.CategoryTheory.ChosenFiniteProducts
import Mathlib.CategoryTheory.Monoidal.Mon_
import Mathlib.CategoryTheory.Monoidal.Yoneda
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Toric.Mathlib.CategoryTheory.Monoidal.Category


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

attribute [instance] monoidOfMon_Class

variable {C : Type*} [Category C] [ChosenFiniteProducts C] {M N : Mon_ C}  [CommMon_Class N.X]

@[reassoc]
lemma Mon_Class.comp_mul {M N O : C} (f g : M ⟶ N) (h : O ⟶ M) [Mon_Class N] :
    h ≫ (f * g) = h ≫ f * h ≫ g :=
  (((yonedaMon.obj (.mk' N)).map (h.op)).hom.map_mul f g)

lemma Mon_Class.one_eq_one {M : C} [Mon_Class M] :
    η = (1 : _ ⟶ M) := by
  show _ = _ ≫ _
  rw [toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]

lemma Mon_.one_eq_one {M : Mon_ C} :
    M.one = 1 :=
  Mon_Class.one_eq_one (M := M.X)

@[reassoc]
lemma Mon_Class.mul_comp {M N O : C} (f g : M ⟶ N) (h : N ⟶ O) [Mon_Class N] [Mon_Class O]
    [IsMon_Hom h] :
    (f * g) ≫ h = (f ≫ h) * g ≫ h :=
  (((yonedaMon.map (Mon_.homMk h)).app (.op M)).hom.map_mul f g)

@[reassoc]
lemma Mon_Class.one_comp {M N O : C} (h : N ⟶ O) [Mon_Class N] [Mon_Class O]
    [IsMon_Hom h] : (1 : M ⟶ N) ≫ h = 1 :=
  ((yonedaMon.map (Mon_.homMk h)).app (.op M)).hom.map_one

instance {M N : C} [Mon_Class N] [CommMon_Class N] : CommMonoid (M ⟶ N) where
  mul_comm f g := by
    show lift _ _ ≫ _ = lift _ _ ≫ _
    conv_lhs => rw [← CommMon_Class.mul_comm N]
    rw [← Category.assoc]
    congr 1
    ext <;> simp

end

namespace Mon_

variable {C : Type*} [Category C] [ChosenFiniteProducts C] {M N : Mon_ C}  [CommMon_Class N.X]

lemma gigaDiagram :
    (α_ _ _ _).hom
    ≫ M.X ◁ (α_ _ _ _).inv
    ≫ M.X ◁ (M.mul ▷ M.X)
    ≫ M.X ◁ M.mul
    ≫ M.mul
      = (M.mul ⊗ M.mul)
        ≫ M.mul := calc
  _ = (α_ _ _ _).hom
        ≫ M.X ◁ ((α_ _ _ _).inv ≫ M.mul ▷ M.X ≫ M.mul)
        ≫ M.mul := by simp [-Mon_.mul_assoc]
  _ = (α_ _ _ _).hom
        ≫ M.X ◁ M.X ◁ M.mul
        ≫ M.X ◁ M.mul
        ≫ M.mul := by
    simp [M.mul_assoc]
  _ = (M.X ⊗ M.X) ◁ M.mul
        ≫ (α_ _ _ _).hom
        ≫ M.X ◁ M.mul
        ≫ M.mul := by simp
  _ = (M.X ⊗ M.X) ◁ M.mul
        ≫ M.mul ▷ M.X
        ≫ M.mul := by simp
  _ = (M.mul ⊗ M.mul) ≫ M.mul := by
    rw [tensorHom_def']
    simp

lemma gigaDiagram2 :
    (α_ _ _ _).hom
    ≫ N.X ◁ (α_ _ _ _).inv
    ≫ N.X ◁ ((β_ _ _).hom ▷ N.X)
    ≫ N.X ◁ (N.mul ▷ N.X)
    ≫ N.X ◁ N.mul
    ≫ N.mul
      = (α_ _ _ _).hom
        ≫ N.X ◁ (α_ _ _ _).inv
        ≫ N.X ◁ (N.mul ▷ N.X)
        ≫ N.X ◁ N.mul
        ≫ N.mul := calc
  _ = (α_ _ _ _).hom
    ≫ N.X ◁ (α_ _ _ _).inv
    ≫ N.X ◁ (((β_ _ _).hom ≫ N.mul) ▷ N.X)
    ≫ N.X ◁ N.mul
    ≫ N.mul := by simp
  _ = (α_ _ _ _).hom
        ≫ N.X ◁ (α_ _ _ _).inv
        ≫ N.X ◁ (N.mul ▷ N.X)
        ≫ N.X ◁ N.mul
        ≫ N.mul := by
    have : N.mul = μ := rfl
    rw [this]
    rw [CommMon_Class.mul_comm N.X]

lemma gigaDiagram3 :
    (α_ _ _ _).hom
    ≫ M.X ◁ (α_ _ _ _).inv
    ≫ M.X ◁ ((β_ _ _).hom ▷ M.X)
    ≫ M.X ◁ (α_ _ _ _).hom
    ≫ (α_ _ _ _).inv
    ≫ (α_ _ _ _).hom
    ≫ M.X ◁ (α_ _ _ _).inv
    ≫ M.X ◁ (M.mul ▷ M.X)
    ≫ M.X ◁ M.mul
    ≫ M.mul
      = (α_ _ _ _).hom
        ≫ M.X ◁ (α_ _ _ _).inv
        ≫ M.X ◁ ((β_ _ _).hom ▷ M.X)
        ≫ M.X ◁ (M.mul ▷ M.X)
        ≫ M.X ◁ M.mul
        ≫ M.mul  := by simp

lemma gigaDiagram4 :
    (α_ _ _ _).hom
    ≫ M.X ◁ (α_ _ _ _).inv
    ≫ M.X ◁ ((β_ _ _).hom ▷ M.X)
    ≫ M.X ◁ (α_ _ _ _).hom
    ≫ (α_ _ _ _).inv
    ≫ (α_ _ _ _).hom
    ≫ M.X ◁ (α_ _ _ _).inv
    ≫ M.X ◁ (M.mul ▷ M.X)
    ≫ M.X ◁ M.mul
    ≫ M.mul
      = (α_ _ _ _).hom
        ≫ M.X ◁ (α_ _ _ _).inv
        ≫ M.X ◁ ((β_ _ _).hom ▷ M.X)
        ≫ M.X ◁ (α_ _ _ _).hom
        ≫ (α_ _ _ _).inv
        ≫ (M.mul ⊗ M.mul)
        ≫ M.mul := by
  rw [gigaDiagram]

lemma gigaOmegaDiagram :
    (N.mul ⊗ N.mul)
    ≫ N.mul
      = (α_ _ _ _).hom
        ≫ N.X ◁ (α_ _ _ _).inv
        ≫ N.X ◁ ((β_ _ _).hom ▷ N.X)
        ≫ N.X ◁ (α_ _ _ _).hom
        ≫ (α_ _ _ _).inv
        ≫ (N.mul ⊗ N.mul)
        ≫ N.mul := by
  nth_rewrite 1 [← gigaDiagram, ← gigaDiagram2, ← gigaDiagram3, gigaDiagram4]
  simp

@[simps]
instance Hom.instMul : Mul (M ⟶ N) where
  mul f g :=
  { hom := f.hom * g.hom
    one_hom := by simp [Mon_.one_eq_one, Mon_Class.comp_mul, Mon_Class.one_comp]
    mul_hom := by
      rw [← lift_fst_comp_snd_comp]
      trans (lift (fst _ _) (snd _ _) ≫ M.mul) ≫ (f.hom * g.hom)
      · simp
      · show (fst _ _ * snd _ _) ≫ (f.hom * g.hom) =
          (fst M.X M.X ≫ (f.hom * g.hom)) * (snd M.X M.X ≫ (f.hom * g.hom))
        simp only [Mon_Class.comp_mul, Mon_Class.mul_comp, mul_mul_mul_comm] }

    /-
      rw [← Category.assoc G.mul]
      simp
      let e := calc
        (H.X ⊗ H.X) ⊗ (H.X ⊗ H.X)
        _ ≅ H.X ⊗ (H.X ⊗ (H.X ⊗ H.X)) := α_ _ _ _
        _ ≅ H.X ⊗ ((H.X ⊗ H.X) ⊗ H.X) := H.X ◁ (α_ _ _ _).symm
        _ ≅ H.X ⊗ ((H.X ⊗ H.X) ⊗ H.X) := H.X ◁ β_ H.X H.X ▷ H.X
        _ ≅ H.X ⊗ (H.X ⊗ (H.X ⊗ H.X)) := H.X ◁ α_ _ _ _
        _ ≅ (H.X ⊗ H.X) ⊗ (H.X ⊗ H.X) := (α_ _ _ _).symm
      calc lift ((f.hom ⊗ f.hom) ≫ H.mul) ((g.hom ⊗ g.hom) ≫ H.mul) ≫ H.mul
      _ = (lift f.hom f.hom ⊗ lift g.hom g.hom) ≫ e.inv ≫ (tensorHom H.mul H.mul) ≫ H.mul := sorry
      _ = ((lift f.hom g.hom ⊗ lift f.hom g.hom) ≫ e.hom) ≫ e.inv ≫ (tensorHom H.mul H.mul) ≫ H.mul := by
        congr!
        sorry
      _ = e.hom ≫ e.inv ≫ (lift f.hom g.hom ⊗ lift f.hom g.hom) ≫ (tensorHom H.mul H.mul) ≫ H.mul := by simp
      _ = (lift f.hom g.hom ⊗ lift f.hom g.hom) ≫ (tensorHom H.mul H.mul) ≫ H.mul := by simp
    -/

end  Mon_

#exit

namespace Grp_

section

open ChosenFiniteProducts MonoidalCategory

variable {C : Type*} [Category C] [ChosenFiniteProducts C] {G H : Mon_ C} [CommMon_Class H.X]


instance instCommGroup_HomToComm (G H : Grp_ C) [CommMon_Class H.X] : CommGroup (G ⟶ H) where
  mul_assoc f g h := sorry
  one := sorry
  one_mul := sorry
  mul_one := sorry
  inv := sorry
  inv_mul_cancel := sorry
  mul_comm := sorry

end
