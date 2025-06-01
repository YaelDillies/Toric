/-
Copyright (c) 2025 Yaël Dillies, Michał Mrugała, Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Michał Mrugała, Andrew Yang
-/
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp_
import Toric.Mathlib.CategoryTheory.Monoidal.Cartesian.Mon_

open CategoryTheory Limits Mon_Class MonoidalCategory CartesianMonoidalCategory Opposite
open scoped Hom

universe v₁ v₂ v₃ u₁ u₂ u₃

scoped[Hom] attribute [instance] Hom.group

namespace CategoryTheory.Functor
variable {C D : Type*} [Category C] [Category D] [CartesianMonoidalCategory C]
  [CartesianMonoidalCategory D] {G : C} [Grp_Class G] (F : C ⥤ D) [F.Monoidal]

scoped[Obj] attribute [instance] CategoryTheory.Functor.obj.instMon_Class

open scoped Obj

/-- The image of a group object under a monoidal functor is a group object. -/
noncomputable abbrev grp_ClassObj : Grp_Class (F.obj G) := (F.mapGrp.obj (.mk' G)).instGrp_ClassX

scoped[Obj] attribute [instance] CategoryTheory.Functor.grp_ClassObj

end CategoryTheory.Functor

section

open CartesianMonoidalCategory MonoidalCategory

variable {C : Type*} [Category C] [CartesianMonoidalCategory C] {G H : Grp_ C}

@[simps]
def Grp_.homMk {G H : C} [Grp_Class G] [Grp_Class H] (f : G ⟶ H) [IsMon_Hom f] :
    Grp_.mk' G ⟶ Grp_.mk' H := Mon_.Hom.mk' f

@[simp] lemma Grp_.homMk_hom' {G H : Grp_ C} (f : G ⟶ H) : homMk f.hom = f := rfl

lemma Grp_.inv_eq_inv {G : Grp_ C} : G.inv = (𝟙 G.X)⁻¹ := Grp_Class.inv_eq_inv (G := G.X)

@[reassoc]
lemma Grp_Class.comp_div {G H K : C} (f g : G ⟶ H) (h : K ⟶ G) [Grp_Class H] :
    h ≫ (f / g) = h ≫ f / h ≫ g :=
  (((yonedaGrp.obj (.mk' H)).map (h.op)).hom.map_div f g)

@[reassoc]
lemma Grp_Class.div_comp {G H K : C} (f g : G ⟶ H) (h : H ⟶ K) [Grp_Class H] [Grp_Class K]
    [IsMon_Hom h] : (f / g) ≫ h = (f ≫ h) / (g ≫ h) :=
    (((yonedaGrp.map (Grp_.homMk h)).app (.op G)).hom.map_div f g)

lemma Grp_Class.inv_eq_comp_inv {G H : C} (f : G ⟶ H) [Grp_Class H] : f ≫ ι = f⁻¹ := rfl

lemma Grp_Class.mul_eq_comp_mul {G H : C} {f g : G ⟶ H} [Grp_Class H] : f * g = lift f g ≫ μ := rfl

attribute [local simp] mul_eq_mul Grp_Class.inv_eq_inv comp_mul comp_mul_assoc
  mul_comp mul_comp_assoc Grp_Class.comp_inv one_eq_one Grp_.inv_eq_inv Mon_.one_eq_one
  Mon_.mul_eq_mul Grp_Class.div_comp Grp_Class.div_comp_assoc one_comp

lemma Grp_Class.mul_inv_rev [BraidedCategory C] {G : C} [Grp_Class G] :
    μ ≫ ι = ((ι : G ⟶ G) ⊗ ι) ≫ (β_ _ _).hom ≫ μ := by
  simp

@[reassoc (attr := simp)]
lemma Grp_Class.one_inv [BraidedCategory C] {G : C} [Grp_Class G] :
    η[G] ≫ ι[G] = η[G] := by
  simp

attribute [local simp] mul_comm mul_div_mul_comm

instance [BraidedCategory C] {G : C} [Grp_Class G] [IsCommMon G] : IsMon_Hom ι[G] where

/-- If `G` is a commutative group object, then `Hom(X, G)` has a commutative group structure. -/
abbrev Hom.commGroup [BraidedCategory C] {G H : C} [Grp_Class H] [IsCommMon H] :
    CommGroup (G ⟶ H) where
  __ := Hom.commMonoid
  inv_mul_cancel f := by simp

scoped[Hom] attribute [instance] Hom.commGroup

@[reassoc]
lemma Grp_Class.comp_zpow {G H K : C} [Grp_Class H] (f : G ⟶ H) (h : K ⟶ G) :
    ∀ n : ℤ, h ≫ f ^ n = (h ≫ f) ^ n
  | (n : ℕ) => by simp [comp_pow]
  | .negSucc n => by simp [comp_pow, comp_inv]

namespace Grp_Class
variable [BraidedCategory C]

instance : Grp_Class (𝟙_ C) where
  inv := 𝟙 _
  left_inv' := toUnit_unique _ _
  right_inv' := toUnit_unique _ _

namespace tensorObj

@[simps inv]
instance {G H : C} [Grp_Class G] [Grp_Class H] : Grp_Class (G ⊗ H) where
  inv := ι ⊗ ι
  left_inv' := by
    have H : ((𝟙 G)⁻¹ ⊗ (𝟙 H)⁻¹) * 𝟙 (G ⊗ H) = 1 := by
      simp only [← tensor_id, ← mul_tensor_mul, inv_mul_cancel, one_tensor_one]
    simpa [mul_tensor_mul, comp_mul, ← tensor_comp, one_eq_one, one_tensor_one]
  right_inv' := by
    have H : 𝟙 (G ⊗ H) * ((𝟙 G)⁻¹ ⊗ (𝟙 H)⁻¹) = 1 := by
      simp only [← tensor_id, ← mul_tensor_mul, mul_inv_cancel, one_tensor_one]
    simpa [mul_tensor_mul, comp_mul, ← tensor_comp, one_eq_one, one_tensor_one]

end tensorObj
end Grp_Class

namespace Grp_

@[simp] lemma mk'_X (G : C) [Grp_Class G] : (mk' G).X = G := rfl

variable [BraidedCategory C] {G H H₁ H₂ : Grp_ C}

@[simps! tensorObj_X tensorHom_hom]
instance instMonoidalCategoryStruct : MonoidalCategoryStruct (Grp_ C) where
  tensorObj G H := mk' (G.X ⊗ H.X)
  tensorHom := tensorHom (C := Mon_ C)
  whiskerRight f _ := whiskerRight (C := Mon_ C) f _
  whiskerLeft _ _ _ := whiskerLeft (C := Mon_ C) _
  tensorUnit := mk' (𝟙_ C)
  associator _ _ _ := (Grp_.fullyFaithfulForget₂Mon_ C).preimageIso (associator _ _ _)
  leftUnitor _ := (Grp_.fullyFaithfulForget₂Mon_ C).preimageIso (leftUnitor _)
  rightUnitor _ := (Grp_.fullyFaithfulForget₂Mon_ C).preimageIso (rightUnitor _)

@[simp] lemma tensorUnit_X : (𝟙_ (Grp_ C)).X = 𝟙_ C := rfl

@[simp] lemma tensorUnit_one : (𝟙_ (Grp_ C)).one = 𝟙 (𝟙_ C) := rfl

@[simp] lemma tensorUnit_mul : (𝟙_ (Grp_ C)).mul = (λ_ (𝟙_ C)).hom := rfl

@[simp] lemma tensorObj_one (G H : Grp_ C) : (G ⊗ H).one = (λ_ (𝟙_ C)).inv ≫ (G.one ⊗ H.one) := rfl

@[simp] lemma tensorObj_mul (G H : Grp_ C) :
    (G ⊗ H).mul = tensorμ G.X H.X G.X H.X ≫ (G.mul ⊗ H.mul) := rfl

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

@[simp] lemma tensor_one (G H : Grp_ C) : (G ⊗ H).one = (λ_ (𝟙_ C)).inv ≫ (G.one ⊗ H.one) := rfl

@[simp] lemma tensor_mul (G H : Grp_ C) :
    (G ⊗ H).mul = tensorμ G.X H.X G.X H.X ≫ (G.mul ⊗ H.mul) := rfl

instance instMonoidalCategory : MonoidalCategory (Grp_ C) where
  tensorHom_def := by intros; ext; simp [tensorHom_def]
  triangle _ _ := by ext; exact triangle _ _

instance instCartesianMonoidalCategory : CartesianMonoidalCategory (Grp_ C) where
  isTerminalTensorUnit :=
    .ofUniqueHom (fun G ↦ toUnit G.toMon_) fun G f ↦ by ext; exact toUnit_unique ..
  fst G H := fst G.toMon_ H.toMon_
  snd G H := snd G.toMon_ H.toMon_
  tensorProductIsBinaryProduct G H :=
    BinaryFan.IsLimit.mk _ (fun {T} f g ↦ .mk (lift f.hom g.hom)
      (by aesop_cat) (by aesop_cat)) (by aesop_cat) (by aesop_cat) (by aesop_cat)
  fst_def G H := Mon_.ext <| fst_def _ _
  snd_def G H := Mon_.ext <| snd_def _ _

@[simp] lemma lift_hom (f : G ⟶ H₁) (g : G ⟶ H₂) : (lift f g).hom = lift f.hom g.hom := rfl
@[simp] lemma fst_hom (G H : Grp_ C) : (fst G H).hom = fst G.X H.X := rfl
@[simp] lemma snd_hom (G H : Grp_ C) : (snd G H).hom = snd G.X H.X := rfl

instance instBraided : BraidedCategory (Grp_ C) where braiding G H := Grp_.mkIso (β_ G.X H.X)

@[simp] lemma braiding_hom_hom (G H : Grp_ C) : (β_ G H).hom.hom = (β_ G.X H.X).hom := rfl
@[simp] lemma braiding_inv_hom (G H : Grp_ C) : (β_ G H).inv.hom = (β_ G.X H.X).inv := rfl

variable [IsCommMon H.X]

namespace Hom

instance : Mon_Class H where
  one := η[H.toMon_]
  mul := μ[H.toMon_]
  one_mul' := Mon_Class.one_mul H.toMon_
  mul_one' := Mon_Class.mul_one H.toMon_
  mul_assoc' := Mon_Class.mul_assoc H.toMon_

@[simp] lemma hom_one : (1 : G ⟶ H).hom = 1 := rfl

@[simp] lemma hom_mul (f g : G ⟶ H) : (f * g).hom = f.hom * g.hom := rfl

@[simp] lemma hom_pow (f : G ⟶ H) (n : ℕ) : (f ^ n).hom = f.hom ^ n := by
  induction n <;> simp [pow_succ, *]

/-- A commutative group object is a group object in the category of group objects. -/
instance : Grp_Class H where inv := .mk H.inv

instance {f : G ⟶ H} [IsCommMon H.X] : IsMon_Hom f.hom⁻¹ where

@[simp] lemma hom_inv (f : G ⟶ H) : f⁻¹.hom = f.hom⁻¹ := rfl
@[simp] lemma hom_div (f g : G ⟶ H) : (f / g).hom = f.hom / g.hom := rfl
@[simp] lemma hom_zpow (f : G ⟶ H) (n : ℤ) : (f ^ n).hom = f.hom ^ n := by cases n <;> simp

end Hom

/-- A commutative group object is a commutative group object in the category of group objects. -/
instance : IsCommMon H where

end Grp_

variable {C : Type*} [Category C] [CartesianMonoidalCategory C] [BraidedCategory C] {G : C}

instance Grp_.mk'.X.instIsComm_Mon [Grp_Class G] [IsCommMon G] : IsCommMon (Grp_.mk' G).X := ‹_›

end

namespace CategoryTheory
variable {C : Type u₁} [Category.{v₁} C] [CartesianMonoidalCategory C]
  {D : Type u₂} [Category.{v₂} D] [CartesianMonoidalCategory D]
  {E : Type u₃} [Category.{v₃} E] [CartesianMonoidalCategory E]

namespace Functor
variable {F F' : C ⥤ D} [F.Monoidal] [F'.Monoidal] {G : D ⥤ E} [G.Monoidal]

open LaxMonoidal Monoidal

protected instance Faithful.mapGrp [F.Faithful] : F.mapGrp.Faithful where
  map_injective {_X _Y} _f _g hfg := F.mapMon.map_injective hfg

protected instance Full.mapGrp [F.Full] [F.Faithful] : F.mapGrp.Full where
  map_surjective := F.mapMon.map_surjective

/-- If `F : C ⥤ D` is a fully faithful monoidal functor, then `Grp(F) : Grp C ⥤ Grp D` is fully
faithful too. -/
protected noncomputable def FullyFaithful.mapGrp (hF : F.FullyFaithful) :
    F.mapGrp.FullyFaithful where
  preimage {X Y} f := Grp_.homMk <| hF.preimage f.hom

open EssImageSubcategory Monoidal in
/-- The essential image of a full and faithful functor between cartesian-monoidal categories is the
same on group objects as on objects. -/
@[simp] lemma essImage_mapGrp [F.Full] [F.Faithful] {G : Grp_ D} :
    F.mapGrp.essImage G ↔ F.essImage G.X where
  mp := by rintro ⟨H, ⟨e⟩⟩; exact ⟨H.X, ⟨(Grp_.forget _).mapIso e⟩⟩
  mpr hG := by
    letI F' := F.toEssImage.asEquivalence
    have : F'.inverse.Monoidal := .ofChosenFiniteProducts _
    refine ⟨F'.inverse.mapGrp.obj <| {
        X := ⟨G.X, hG⟩
        one := G.one
        mul := G.mul
        one_mul := by simpa only [whiskerRight_def] using G.one_mul
        mul_one := by simpa only [whiskerLeft_def] using G.mul_one
        mul_assoc := by
          simpa only [whiskerLeft_def, whiskerRight_def, associator_hom_def] using G.mul_assoc
        inv := G.inv
        left_inv := by simpa only [lift_def, toUnit_def] using G.left_inv
        right_inv := by simpa only [lift_def, toUnit_def] using G.right_inv
      }, ⟨Grp_.mkIso
        ((ObjectProperty.ι _).mapIso <| F'.counitIso.app ⟨G.X, hG⟩) ?_ ?_⟩⟩
    · simp
      erw [F'.counitIso.hom.naturality (X := 𝟙_ F.EssImageSubcategory) (Y := ⟨G.X, hG⟩) G.one]
      have : ε F ≫ F.map (ε F'.inverse) ≫ F'.counitIso.hom.app (𝟙_ F.EssImageSubcategory) = 𝟙 _ :=
        toUnit_unique ..
      apply_fun (· ≫ (G.one : 𝟙_ F.EssImageSubcategory ⟶ ⟨G.X, hG⟩)) at this
      simpa using this
    · simp
      erw [F'.counitIso.hom.naturality (X := ⟨G.X, hG⟩ ⊗ ⟨G.X, hG⟩) (Y := ⟨G.X, hG⟩) G.mul]
      have :
        «μ» F _ _ ≫ F.map («μ» F'.inverse ⟨G.X, hG⟩ ⟨G.X, hG⟩) ≫ F'.counitIso.hom.app _ =
          F'.counitIso.hom.app _ ⊗ F'.counitIso.hom.app _ := by
        --erw [F'.functor_map_μ_inverse_comp_counitIso_hom_app_tensor]
        simp
        refine hom_ext _ _ ?_ ?_
        · refine Eq.trans ?_ (tensorHom_fst (F'.counitIso.hom.app ⟨G.X, hG⟩)
            (F'.counitIso.hom.app ⟨G.X, hG⟩)).symm
          sorry
        · sorry
      apply_fun (· ≫ (G.mul : (⟨G.X, hG⟩ ⊗ ⟨G.X, hG⟩ : F.EssImageSubcategory) ⟶ ⟨G.X, hG⟩)) at this
      sorry

end Functor
end CategoryTheory
