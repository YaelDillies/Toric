import Mathlib.CategoryTheory.Monoidal.Grp_
import Toric.Mathlib.CategoryTheory.Monoidal.Mon_

/-! ### Transfer monoid/group objects along an iso -/

section
open CategoryTheory CartesianMonoidalCategory
open scoped Mon_Class

def Grp_Class.ofIso {C : Type*} [Category C] [CartesianMonoidalCategory C] {G X : C} (e : G ≅ X)
    [Grp_Class G] : Grp_Class X where
  toMon_Class := .ofIso e
  inv := e.inv ≫ ι[G] ≫ e.hom
  left_inv := by simp only [Mon_Class.ofIso, lift_map_assoc, Category.assoc, Iso.hom_inv_id,
    Category.comp_id, Category.id_comp, lift_comp_inv_left_assoc]
  right_inv := by simp [Mon_Class.ofIso]

end

/-! ### Pushforward of a group object -/

namespace CategoryTheory.Functor
variable {C D : Type*} [Category C] [Category D] [CartesianMonoidalCategory C]
  [CartesianMonoidalCategory D] {G : C} [Grp_Class G] (F : C ⥤ D) [F.Monoidal]

open scoped Obj

/-- The image of a group object under a monoidal functor is a group object. -/
noncomputable abbrev grp_ClassObj : Grp_Class (F.obj G) := (F.mapGrp.obj ⟨G⟩).grp

scoped[Obj] attribute [instance] CategoryTheory.Functor.grp_ClassObj

end CategoryTheory.Functor

/-! ### `Grp_ C` is cartesian-monoidal -/

namespace Grp_
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Mon_Class

variable {C : Type*} [Category C] [CartesianMonoidalCategory C] [BraidedCategory C]
  {G H H₁ H₂ : Grp_ C}

@[simps! tensorObj_X tensorHom_hom]
instance instMonoidalCategoryStruct : MonoidalCategoryStruct (Grp_ C) where
  tensorObj G H := ⟨G.X ⊗ H.X⟩
  tensorHom := tensorHom (C := Mon_ C)
  whiskerRight f G := whiskerRight (C := Mon_ C) f G.toMon_
  whiskerLeft G _ _ f := MonoidalCategoryStruct.whiskerLeft (C := Mon_ C) G.toMon_ f
  tensorUnit := ⟨𝟙_ C⟩
  associator X Y Z :=
    (Grp_.fullyFaithfulForget₂Mon_ C).preimageIso (associator X.toMon_ Y.toMon_ Z.toMon_)
  leftUnitor G := (Grp_.fullyFaithfulForget₂Mon_ C).preimageIso (leftUnitor G.toMon_)
  rightUnitor G := (Grp_.fullyFaithfulForget₂Mon_ C).preimageIso (rightUnitor G.toMon_)

@[simp] lemma tensorUnit_X : (𝟙_ (Grp_ C)).X = 𝟙_ C := rfl

@[simp] lemma tensorUnit_one : η[(𝟙_ (Grp_ C)).X] = η[𝟙_ C] := rfl
@[simp] lemma tensorUnit_mul : μ[(𝟙_ (Grp_ C)).X] = μ[𝟙_ C] := rfl

@[simp] lemma tensorObj_one (G H : Grp_ C) : η[(G ⊗ H).X] = η[G.X ⊗ H.X] := rfl
@[simp] lemma tensorObj_mul (G H : Grp_ C) : μ[(G ⊗ H).X] = μ[G.X ⊗ H.X] := rfl

@[simp] lemma whiskerLeft_hom {G H : Grp_ C} (f : G ⟶ H) (I : Grp_ C) :
    (f ▷ I).hom = f.hom ▷ I.X := rfl

@[simp] lemma whiskerRight_hom (G : Grp_ C) {H I : Grp_ C} (f : H ⟶ I) :
    (G ◁ f).hom = G.X ◁ f.hom := rfl

@[simp] lemma leftUnitor_hom_hom (G : Grp_ C) : (λ_ G).hom.hom = (λ_ G.X).hom := rfl
@[simp] lemma leftUnitor_inv_hom (G : Grp_ C) : (λ_ G).inv.hom = (λ_ G.X).inv := rfl
@[simp] lemma rightUnitor_hom_hom (G : Grp_ C) : (ρ_ G).hom.hom = (ρ_ G.X).hom := rfl
@[simp] lemma rightUnitor_inv_hom (G : Grp_ C) : (ρ_ G).inv.hom = (ρ_ G.X).inv := rfl

@[simp] lemma associator_hom_hom (G H I : Grp_ C) : (α_ G H I).hom.hom = (α_ G.X H.X I.X).hom := rfl
@[simp] lemma associator_inv_hom (G H I : Grp_ C) : (α_ G H I).inv.hom = (α_ G.X H.X I.X).inv := rfl

instance instMonoidalCategory : MonoidalCategory (Grp_ C) where
  tensorHom_def := by intros; ext; simp [tensorHom_def]
  triangle _ _ := by ext; exact triangle _ _

instance instCartesianMonoidalCategory : CartesianMonoidalCategory (Grp_ C) where
  isTerminalTensorUnit :=
    .ofUniqueHom (fun G ↦ toUnit G.toMon_) fun G f ↦ by ext; exact toUnit_unique ..
  fst G H := fst G.toMon_ H.toMon_
  snd G H := snd G.toMon_ H.toMon_
  tensorProductIsBinaryProduct G H :=
    BinaryFan.IsLimit.mk _ (fun {T} f g ↦ .mk (lift f.hom g.hom))
      (by aesop_cat) (by aesop_cat) (by aesop_cat)
  fst_def G H := Mon_.Hom.ext <| fst_def _ _
  snd_def G H := Mon_.Hom.ext <| snd_def _ _

@[simp] lemma lift_hom (f : G ⟶ H₁) (g : G ⟶ H₂) : (lift f g).hom = lift f.hom g.hom := rfl
@[simp] lemma fst_hom (G H : Grp_ C) : (fst G H).hom = fst G.X H.X := rfl
@[simp] lemma snd_hom (G H : Grp_ C) : (snd G H).hom = snd G.X H.X := rfl

@[simps]
instance : (forget₂Mon_ C).Monoidal where
  ε := 𝟙 _
  «μ» G H := 𝟙 _
  «η» := 𝟙 _
  δ G H := 𝟙 _

attribute [local simp] one_eq_one mul_eq_mul comp_mul in
instance instBraidedCategory : BraidedCategory (Grp_ C) :=
  .ofFaithful (forget₂Mon_ C) fun G H ↦ Grp_.mkIso (β_ G.X H.X)

@[simp] lemma braiding_hom_hom (G H : Grp_ C) : (β_ G H).hom.hom = (β_ G.X H.X).hom := rfl
@[simp] lemma braiding_inv_hom (G H : Grp_ C) : (β_ G H).inv.hom = (β_ G.X H.X).inv := rfl

end Grp_

-- TODO: Make `Grp_.toMon_` an abbrev in mathlib.
set_option allowUnsafeReducibility true in
attribute [reducible] Grp_.toMon_

namespace CategoryTheory.Functor
universe v₁ v₂ u₁ u₂
variable {C : Type u₁} [Category.{v₁} C] [CartesianMonoidalCategory C]
  {D : Type u₂} [Category.{v₂} D] [CartesianMonoidalCategory D]
  {F : C ⥤ D} [F.Monoidal]

open LaxMonoidal Monoidal

/-! ### Essential image computation -/

/-- The essential image of a full and faithful functor between cartesian-monoidal categories is the
same on group objects as on objects. -/
@[simp] lemma essImage_mapGrp [F.Full] [F.Faithful] {G : Grp_ D} :
    F.mapGrp.essImage G ↔ F.essImage G.X where
  mp := by rintro ⟨H, ⟨e⟩⟩; exact ⟨H.X, ⟨(Grp_.forget _).mapIso e⟩⟩
  mpr := by
    rintro ⟨H, ⟨e⟩⟩
    letI h₁ := Grp_Class.ofIso e.symm
    letI h₂ := FullyFaithful.grp_Class (.ofFullyFaithful F) H
    refine ⟨⟨H⟩, ⟨Grp_.mkIso e ?_ ?_⟩⟩ <;>
      simp [Grp_Class.ofIso, Mon_Class.ofIso, FullyFaithful.mon_Class, FullyFaithful.grp_Class,
        h₁, h₂]

/-! ### `mapGrp` is braided -/

variable [BraidedCategory C] [BraidedCategory D] (F : C ⥤ D) [F.Braided]

noncomputable instance mapGrp.instMonoidal : F.mapGrp.Monoidal :=
  Functor.CoreMonoidal.toMonoidal
  { εIso := (Grp_.fullyFaithfulForget₂Mon_ _).preimageIso (εIso F.mapMon)
    μIso X Y := (Grp_.fullyFaithfulForget₂Mon_ _).preimageIso (μIso F.mapMon X.toMon_ Y.toMon_)
    μIso_hom_natural_left f Z := by convert μ_natural_left F.mapMon f Z.toMon_ using 1
    μIso_hom_natural_right Z f := by convert μ_natural_right F.mapMon Z.toMon_ f using 1
    associativity X Y Z := by convert associativity F.mapMon X.toMon_ Y.toMon_ Z.toMon_ using 1
    left_unitality X := by convert left_unitality F.mapMon X.toMon_ using 1
    right_unitality X := by convert right_unitality F.mapMon X.toMon_ using 1 }

noncomputable instance mapGrp.instBraided : F.mapGrp.Braided where
  braided X Y := by convert Braided.braided (F := F.mapMon) X.toMon_ Y.toMon_ using 1

end CategoryTheory.Functor
