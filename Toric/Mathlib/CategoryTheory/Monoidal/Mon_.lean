/-
Copyright (c) 2025 Yaël Dillies, Michał Mrugała, Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Michał Mrugała, Andrew Yang
-/
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Monoidal.Yoneda

open CategoryTheory ChosenFiniteProducts Mon_Class MonoidalCategory

section

variable {C : Type*} [Category C] [MonoidalCategory C]

namespace Mon_Class

theorem mul_assoc_flip (X : C) [Mon_Class X] : X ◁ μ ≫ μ = (α_ X X X).inv ≫ μ ▷ X ≫ μ := by simp

end Mon_Class

namespace Mon_

-- Rewrite Mon_.mul_assoc_flip to this
example {M : Mon_ C} : (M.X ◁ M.mul) ≫ M.mul = (α_ M.X M.X M.X).inv ≫ (M.mul ▷ M.X) ≫ M.mul :=
  Mon_Class.mul_assoc_flip M.X

end Mon_

end

section

variable {C : Type*} [Category C] [MonoidalCategory C] {M N : Mon_ C}

instance {M N : Mon_ C} (f : M ⟶ N) : IsMon_Hom f.hom := ⟨f.2, f.3⟩

@[simps]
def Mon_.homMk {M N : C} [Mon_Class M] [Mon_Class N] (f : M ⟶ N) [IsMon_Hom f] :
    Mon_.mk' M ⟶ Mon_.mk' N := .mk f

end
section

attribute [local instance] monoidOfMon_Class

variable {C : Type*} [Category C] [ChosenFiniteProducts C] {M N : Mon_ C} [IsCommMon N.X]

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
    h ≫ (1 : N ⟶ O) = 1 := ((yonedaMon.obj (.mk' O)).map (h.op)).hom.map_one

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

end Mon_.Hom

section
variable {C : Type*} [Category C] [ChosenFiniteProducts C] {G : C}

instance [Mon_Class G] [IsCommMon G] : IsCommMon (Mon_.mk' G).X := ‹_›

end

open Limits

namespace CategoryTheory.Functor
universe v₁ v₂ v₃ u₁ u₂ u₃

section MonoidalCategory
variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
variable {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]
variable {E : Type u₃} [Category.{v₃} E] [MonoidalCategory E]
variable (F F' : C ⥤ D) (G : D ⥤ E)

open LaxMonoidal

section objMon
variable [F.LaxMonoidal] (X : C) [Mon_Class X]

instance obj.instMon_Class : Mon_Class (F.obj X) where
  one := ε F ≫ F.map η
  mul := LaxMonoidal.μ F X X ≫ F.map μ
  one_mul' := by simp [← F.map_comp]
  mul_one' := by simp [← F.map_comp]
  mul_assoc' := by
    simp_rw [comp_whiskerRight, Category.assoc, μ_natural_left_assoc,
      MonoidalCategory.whiskerLeft_comp, Category.assoc, μ_natural_right_assoc]
    slice_lhs 3 4 => rw [← F.map_comp, Mon_Class.mul_assoc]
    simp

@[reassoc (attr := simp)]
lemma ε_comp_map_η : ε F ≫ F.map η = (η : 𝟙_ D ⟶ F.obj X) := rfl

@[reassoc (attr := simp)]
lemma μ_comp_map_μ (X : C) [Mon_Class X] : LaxMonoidal.μ F X X ≫ F.map μ = μ := rfl

end objMon

protected instance Faithful.mapMon [F.LaxMonoidal] [F.Faithful] : F.mapMon.Faithful where
  map_injective {_X _Y} _f _g hfg := Mon_.Hom.ext <| map_injective congr(($hfg).hom)

protected instance Full.mapMon [F.Monoidal] [F.Full] [F.Faithful] : F.mapMon.Full where
  map_surjective {X Y} f :=
    let ⟨g, hg⟩ := F.map_surjective f.hom
    ⟨{
      hom := g
      one_hom := F.map_injective <| by simpa [← hg, cancel_epi] using f.one_hom
      mul_hom := F.map_injective <| by simpa [← hg, cancel_epi] using f.mul_hom
    }, Mon_.Hom.ext hg⟩

instance FullyFaithful.isMon_Hom_preimage [F.Monoidal] (hF : F.FullyFaithful) {X Y : C}
    [Mon_Class X] [Mon_Class Y] (f : F.obj X ⟶ F.obj Y) [IsMon_Hom f] :
    IsMon_Hom (hF.preimage f) where
  one_hom := hF.map_injective <| by simp [← cancel_epi (ε F)]
  mul_hom := hF.map_injective <| by simp [← μ_natural_assoc, ← cancel_epi (LaxMonoidal.μ F ..)]

protected def FullyFaithful.mapMon [F.Monoidal] (hF : F.FullyFaithful) :
    F.mapMon.FullyFaithful where
  preimage {X Y} f := Mon_.homMk <| hF.preimage f.hom

@[simps!]
noncomputable def mapMonIdIso : mapMon (𝟭 C) ≅ 𝟭 (Mon_ C) :=
  NatIso.ofComponents fun X ↦ Mon_.mkIso (.refl _) (by simp) (by simp)

@[simps!]
noncomputable def mapMonCompIso [F.LaxMonoidal] [G.LaxMonoidal] :
    (F ⋙ G).mapMon ≅ F.mapMon ⋙ G.mapMon :=
  NatIso.ofComponents fun X ↦ Mon_.mkIso (.refl _) (by simp) (by simp)

end MonoidalCategory

variable {C : Type u₁} [Category.{v₁} C] [ChosenFiniteProducts C]
variable {D : Type u₂} [Category.{v₂} D] [ChosenFiniteProducts D]
variable {E : Type u₃} [Category.{v₃} E] [ChosenFiniteProducts E]
variable (F F' : C ⥤ D) [PreservesFiniteProducts F] [PreservesFiniteProducts F']
variable (G : D ⥤ E) [PreservesFiniteProducts G]

attribute [local instance] monoidalOfChosenFiniteProducts

variable {F F'} in
@[simps!]
noncomputable def mapMonNatTrans (f : F ⟶ F') : F.mapMon ⟶ F'.mapMon where
  app X := .mk (f.app _)

variable {F F'} in
@[simps!]
noncomputable def mapMonNatIso (e : F ≅ F') : F.mapMon ≅ F'.mapMon :=
  NatIso.ofComponents (fun X ↦ Mon_.mkIso (e.app _)) fun {X Y} f ↦ by ext; simp

end CategoryTheory.Functor

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Equivalence
variable {C : Type u₁} [Category.{v₁} C] [ChosenFiniteProducts C]
variable {D : Type u₂} [Category.{v₂} D] [ChosenFiniteProducts D]

attribute [local instance] Functor.monoidalOfChosenFiniteProducts

-- FIXME: There is a diamond between `LaxMonoidal.id` and `Functor.monoidalOfChosenFiniteProducts`
noncomputable def mapMon (e : C ≌ D) : Mon_ C ≌ Mon_ D where
  functor := e.functor.mapMon
  inverse := e.inverse.mapMon
  unitIso := sorry
    -- Functor.mapMonIdIso.symm ≪≫ Functor.mapMonNatIso e.unitIso ≪≫ Functor.mapMonCompIso _ _
  counitIso := sorry
    -- (Functor.mapMonCompIso _ _).symm ≪≫ Functor.mapMonNatIso e.counitIso ≪≫ Functor.mapMonIdIso
  functor_unitIso_comp := sorry

end CategoryTheory.Equivalence

namespace CategoryTheory.ChosenFiniteProducts
variable {C : Type u₁} [Category.{v₁} C] [ChosenFiniteProducts C]
variable {D : Type u₂} [Category.{v₂} D] [ChosenFiniteProducts D]
variable (F : C ⥤ D) [PreservesFiniteProducts F]

attribute [local instance] Functor.monoidalOfChosenFiniteProducts

open Functor LaxMonoidal Monoidal

@[reassoc (attr := simp)]
lemma preservesTerminalIso_inv_comp_map_η (X : C) [Mon_Class X] :
    (preservesTerminalIso F).inv ≫ F.map η = (η : 𝟙_ D ⟶ F.obj X) := by
  simp [← ε_of_chosenFiniteProducts]

@[reassoc (attr := simp)]
lemma preservesProductIso_inv_comp_map_η (X : C) [Mon_Class X] :
    (prodComparisonIso F X X).inv ≫ F.map μ = μ := by
  simp [← μ_of_chosenFiniteProducts]

end CategoryTheory.ChosenFiniteProducts
