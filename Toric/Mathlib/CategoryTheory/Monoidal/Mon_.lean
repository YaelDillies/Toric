/-
Copyright (c) 2025 Yaël Dillies, Michał Mrugała, Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Michał Mrugała, Andrew Yang
-/
import Mathlib.CategoryTheory.Monoidal.Mon_

open CategoryTheory Mon_Class MonoidalCategory

assert_not_exists ChosenFiniteProducts

section
variable {C : Type*} [Category C] [MonoidalCategory C]

namespace Mon_Class

theorem mul_assoc_flip (X : C) [Mon_Class X] : X ◁ μ ≫ μ = (α_ X X X).inv ≫ μ ▷ X ≫ μ := by simp

end Mon_Class

variable [BraidedCategory C] {G : C}

instance Mon_.mk'.X.instIsComm_Mon [Mon_Class G] [IsCommMon G] : IsCommMon (Mon_.mk' G).X := ‹_›

end

namespace Mon_
variable {C : Type*} [Category C] [MonoidalCategory C] {M N : Mon_ C}

instance (f : M ⟶ N) : IsMon_Hom f.hom := ⟨f.2, f.3⟩

/-- Construct a morphism `M ⟶ N` of `Mon_ C` from a map `f : M ⟶ N` and a `IsMon_Hom f` instance. -/
abbrev Hom.mk' {M N : C} [Mon_Class M] [Mon_Class N] (f : M ⟶ N) [IsMon_Hom f] :
    Hom (.mk' M) (.mk' N) := .mk f

-- TODO: Rewrite `Mon_.mul_assoc_flip` to this
example : (M.X ◁ M.mul) ≫ M.mul = (α_ M.X M.X M.X).inv ≫ (M.mul ▷ M.X) ≫ M.mul :=
  Mon_Class.mul_assoc_flip M.X

end Mon_

open Limits

namespace CategoryTheory.Functor
universe v₁ v₂ v₃ u₁ u₂ u₃
variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
variable {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]
variable {E : Type u₃} [Category.{v₃} E] [MonoidalCategory E]
variable (F F' : C ⥤ D) (G : D ⥤ E)

open LaxMonoidal

section objMon
variable [F.LaxMonoidal] (X : C) [Mon_Class X]

/-- The image of a monoid object under a lax monoidal functor is a monoid object. -/
abbrev obj.instMon_Class : Mon_Class (F.obj X) where
  one := ε F ≫ F.map η
  mul := LaxMonoidal.μ F X X ≫ F.map μ
  one_mul' := by simp [← F.map_comp]
  mul_one' := by simp [← F.map_comp]
  mul_assoc' := by
    simp_rw [comp_whiskerRight, Category.assoc, μ_natural_left_assoc,
      MonoidalCategory.whiskerLeft_comp, Category.assoc, μ_natural_right_assoc]
    slice_lhs 3 4 => rw [← F.map_comp, Mon_Class.mul_assoc]
    simp

attribute [local instance] obj.instMon_Class

@[reassoc, simp] lemma obj.η_def : (η : 𝟙_ D ⟶ F.obj X) = ε F ≫ F.map η := rfl
@[reassoc, simp] lemma obj.μ_def : μ = LaxMonoidal.μ F X X ≫ F.map μ := rfl

end objMon

attribute [local instance] obj.instMon_Class

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
  one_hom := hF.map_injective <| by simp [← obj.η_def_assoc, ← obj.η_def, ← cancel_epi (ε F)]
  mul_hom := hF.map_injective <| by
    simp [← obj.μ_def_assoc, ← obj.μ_def, ← μ_natural_assoc, ← cancel_epi (LaxMonoidal.μ F ..)]

protected def FullyFaithful.mapMon [F.Monoidal] (hF : F.FullyFaithful) :
    F.mapMon.FullyFaithful where
  preimage {X Y} f := .mk' <| hF.preimage f.hom

@[simps!]
noncomputable def mapMonIdIso : mapMon (𝟭 C) ≅ 𝟭 (Mon_ C) :=
  NatIso.ofComponents fun X ↦ Mon_.mkIso (.refl _)

@[simps!]
noncomputable def mapMonCompIso [F.LaxMonoidal] [G.LaxMonoidal] :
    (F ⋙ G).mapMon ≅ F.mapMon ⋙ G.mapMon :=
  NatIso.ofComponents fun X ↦ Mon_.mkIso (.refl _)

end CategoryTheory.Functor
