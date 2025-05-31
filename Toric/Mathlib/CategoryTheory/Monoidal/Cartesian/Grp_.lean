/-
Copyright (c) 2025 Yaël Dillies, Michał Mrugała, Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Michał Mrugała, Andrew Yang
-/
import Mathlib.Algebra.Category.Grp.CartesianMonoidal
import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp_
import Mathlib.CategoryTheory.Monoidal.FunctorCategory
import Toric.Mathlib.CategoryTheory.Monoidal.Cartesian.Mon_

section yoneda


/-!
# Yoneda embedding of `Grp_ C`

We show that group objects are exactly those whose yoneda presheaf is a presheaf of groups,
by constructing the yoneda embedding `Grp_ C ⥤ Cᵒᵖ ⥤ GrpCat.{v}` and
showing that it is fully faithful and its (essential) image is the representable functors.

-/

open CategoryTheory Limits Mon_Class MonoidalCategory CartesianMonoidalCategory Opposite
open scoped Hom Obj

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

lemma Grp_Class.mul_inv_rev [BraidedCategory C] {G : C} [Grp_Class G] :
    μ ≫ ι = ((ι : G ⟶ G) ⊗ ι) ≫ (β_ _ _).hom ≫ μ := by
  calc
    _ = ((fst G G) * (snd G G)) ≫ ι := by rw [mul_eq_mul]
    _ = (snd G G)⁻¹ * (fst G G)⁻¹ := by rw [Grp_Class.inv_eq_comp_inv]; simp
    _ = lift (snd G G ≫ ι) (fst G G ≫ ι) ≫ μ := rfl
    _ = lift (fst G G ≫ ι) (snd G G ≫ ι) ≫ (β_ G G).hom ≫ μ := by simp
    _ = ((ι : G ⟶ G) ⊗ ι) ≫ (β_ _ _).hom ≫ μ := by simp

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
section BraidedCategory

variable [BraidedCategory C]

theorem Mon_tensor_one_mul (M N : C) [Mon_Class M] [Mon_Class N] :
    (((λ_ (𝟙_ C)).inv ≫ (η[M] ⊗ η[N])) ▷ (M ⊗ N)) ≫
        tensorμ M N M N ≫ (μ ⊗ μ) =
      (λ_ (M ⊗ N)).hom := by
  simp only [comp_whiskerRight_assoc]
  slice_lhs 2 3 => rw [tensorμ_natural_left]
  slice_lhs 3 4 => rw [← tensor_comp, one_mul, one_mul]
  symm
  exact tensor_left_unitality M N

theorem Mon_tensor_mul_one (M N : C) [Mon_Class M] [Mon_Class N] :
    (M ⊗ N) ◁ ((λ_ (𝟙_ C)).inv ≫ (η[M] ⊗ η[N])) ≫
        tensorμ M N M N ≫ (μ[M] ⊗ μ[N]) =
      (ρ_ (M ⊗ N)).hom := by
  simp only [MonoidalCategory.whiskerLeft_comp_assoc]
  slice_lhs 2 3 => rw [tensorμ_natural_right]
  slice_lhs 3 4 => rw [← tensor_comp, mul_one, mul_one]
  symm
  exact tensor_right_unitality M N

theorem Mon_tensor_mul_assoc (M N : C) [Mon_Class M] [Mon_Class N] :
    ((tensorμ M N M N ≫ (μ ⊗ μ)) ▷ (M ⊗ N)) ≫
        tensorμ M N M N ≫ (μ ⊗ μ) =
      (α_ (M ⊗ N : C) (M ⊗ N) (M ⊗ N)).hom ≫
        ((M ⊗ N : C) ◁ (tensorμ M N M N ≫ (μ ⊗ μ))) ≫
          tensorμ M N M N ≫ (μ ⊗ μ) := by
  simp only [comp_whiskerRight_assoc, MonoidalCategory.whiskerLeft_comp_assoc]
  slice_lhs 2 3 => rw [tensorμ_natural_left]
  slice_lhs 3 4 => rw [← tensor_comp, mul_assoc, mul_assoc, tensor_comp, tensor_comp]
  slice_lhs 1 3 => rw [tensor_associativity]
  slice_lhs 3 4 => rw [← tensorμ_natural_right]
  simp

theorem mul_associator {M N P : C} [Mon_Class M] [Mon_Class N] [Mon_Class P] :
    (tensorμ (M ⊗ N) P (M ⊗ N) P ≫
          (tensorμ M N M N ≫ (μ ⊗ μ) ⊗ μ)) ≫
        (α_ M N P).hom =
      ((α_ M N P).hom ⊗ (α_ M N P).hom) ≫
        tensorμ M (N ⊗ P) M (N ⊗ P) ≫
          (μ ⊗ tensorμ N P N P ≫ (μ ⊗ μ)) := by
  simp only [tensor_obj, prodMonoidal_tensorObj, Category.assoc]
  slice_lhs 2 3 => rw [← Category.id_comp μ[P], tensor_comp]
  slice_lhs 3 4 => rw [associator_naturality]
  slice_rhs 3 4 => rw [← Category.id_comp μ, tensor_comp]
  simp only [tensorHom_id, id_tensorHom]
  slice_lhs 1 3 => rw [associator_monoidal]
  simp only [Category.assoc]

theorem mul_leftUnitor {M : C} [Mon_Class M] :
    (tensorμ (𝟙_ C) M (𝟙_ C) M ≫ ((λ_ (𝟙_ C)).hom ⊗ μ)) ≫ (λ_ M).hom =
      ((λ_ M).hom ⊗ (λ_ M).hom) ≫ μ := by
  rw [← Category.comp_id (λ_ (𝟙_ C)).hom, ← Category.id_comp μ, tensor_comp]
  simp only [tensorHom_id, id_tensorHom]
  slice_lhs 3 4 => rw [leftUnitor_naturality]
  slice_lhs 1 3 => rw [← leftUnitor_monoidal]
  simp only [Category.assoc, Category.id_comp]

theorem mul_rightUnitor {M : C} [Mon_Class M] :
    (tensorμ M (𝟙_ C) M (𝟙_ C) ≫ (μ ⊗ (λ_ (𝟙_ C)).hom)) ≫ (ρ_ M).hom =
      ((ρ_ M).hom ⊗ (ρ_ M).hom) ≫ μ := by
  rw [← Category.id_comp μ, ← Category.comp_id (λ_ (𝟙_ C)).hom, tensor_comp]
  simp only [tensorHom_id, id_tensorHom]
  slice_lhs 3 4 => rw [rightUnitor_naturality]
  slice_lhs 1 3 => rw [← rightUnitor_monoidal]
  simp only [Category.assoc, Category.id_comp]

namespace tensorObj

@[simps inv]
instance {G H : C} [Grp_Class G] [Grp_Class H] : Grp_Class (G ⊗ H) where
  inv := ι ⊗ ι
  left_inv' := by simp [← tensor_id, -tensorHom_id, -id_tensorHom, ← tensor_comp]; simp; sorry
  right_inv' := by simp [← tensor_id, -tensorHom_id, -id_tensorHom, ← tensor_comp]; simp; sorry

end tensorObj
end BraidedCategory

end Grp_Class

namespace Grp_

@[simp] lemma mk'_X (G : C) [Grp_Class G] : (mk' G).X = G := rfl

variable [BraidedCategory C] {G H H₁ H₂ : Grp_ C}

variable [BraidedCategory C]

@[simps! tensorObj_X tensorHom_hom]
instance instMonoidalCategoryStruct : MonoidalCategoryStruct (Grp_ C) where
  tensorObj G H := mk' (G.X ⊗ H.X)
  tensorHom := tensorHom (C := Mon_ C)
  whiskerRight f _ := whiskerRight (C := Mon_ C) f _
  whiskerLeft _ _ _ := whiskerLeft (C := Mon_ C) _
  tensorUnit := mk' (𝟙_ C)
  associator G H I := Mon_.mkIso' <| associator G.X H.X I.X
  leftUnitor M := mkIso' <| leftUnitor M.X
  rightUnitor M := mkIso' <| rightUnitor M.X

@[simp]
theorem tensorUnit_X : (𝟙_ (Grp_ C)).X = 𝟙_ C := rfl

@[simp]
theorem tensorUnit_one : (𝟙_ (Grp_ C)).one = 𝟙 (𝟙_ C) := rfl

@[simp]
theorem tensorUnit_mul : (𝟙_ (Grp_ C)).mul = (λ_ (𝟙_ C)).hom := rfl

@[simp]
theorem tensorObj_one (X Y : Grp_ C) : (X ⊗ Y).one = (λ_ (𝟙_ C)).inv ≫ (X.one ⊗ Y.one) := rfl

@[simp]
theorem tensorObj_mul (X Y : Grp_ C) :
    (X ⊗ Y).mul = tensorμ X.X Y.X X.X Y.X ≫ (X.mul ⊗ Y.mul) := rfl

@[simp]
theorem whiskerLeft_hom {X Y : Grp_ C} (f : X ⟶ Y) (Z : Grp_ C) :
    (f ▷ Z).hom = f.hom ▷ Z.X := by
  rfl

@[simp]
theorem whiskerRight_hom (X : Grp_ C) {Y Z : Grp_ C} (f : Y ⟶ Z) :
    (X ◁ f).hom = X.X ◁ f.hom := by
  rfl

@[simp]
theorem leftUnitor_hom_hom (X : Grp_ C) : (λ_ X).hom.hom = (λ_ X.X).hom := rfl

@[simp]
theorem leftUnitor_inv_hom (X : Grp_ C) : (λ_ X).inv.hom = (λ_ X.X).inv := rfl

@[simp]
theorem rightUnitor_hom_hom (X : Grp_ C) : (ρ_ X).hom.hom = (ρ_ X.X).hom := rfl

@[simp]
theorem rightUnitor_inv_hom (X : Grp_ C) : (ρ_ X).inv.hom = (ρ_ X.X).inv := rfl

@[simp]
theorem associator_hom_hom (X Y Z : Grp_ C) : (α_ X Y Z).hom.hom = (α_ X.X Y.X Z.X).hom := rfl

@[simp]
theorem associator_inv_hom (X Y Z : Grp_ C) : (α_ X Y Z).inv.hom = (α_ X.X Y.X Z.X).inv := rfl

@[simp]
theorem tensor_one (M N : Grp_ C) : (M ⊗ N).one = (λ_ (𝟙_ C)).inv ≫ (M.one ⊗ N.one) := rfl

@[simp]
theorem tensor_mul (M N : Grp_ C) : (M ⊗ N).mul =
    tensorμ M.X N.X M.X N.X ≫ (M.mul ⊗ N.mul) := rfl

instance monMonoidal : MonoidalCategory (Grp_ C) where
  tensorHom_def := by intros; ext; simp [tensorHom_def]


instance instCartesianMonoidalCategory : CartesianMonoidalCategory (Grp_ C) where
  isTerminalTensorUnit :=
    .ofUniqueHom (fun G ↦ toUnit G.toMon_) fun G f ↦ by ext; exact toUnit_unique ..
  fst G H := fst G.toMon_ H.toMon_
  snd G H := snd G.toMon_ H.toMon_
  tensorProductIsBinaryProduct G H :=
    BinaryFan.IsLimit.mk _ (fun {T} f g ↦ .mk (lift f.hom g.hom)
      (by simp; ext <;> simp [toUnit_unique _ (𝟙 _)])
      (by simp; ext <;> simp [toUnit_unique _ (𝟙 _), ← tensor_comp_assoc]))
      (by aesop_cat) (by aesop_cat) (by aesop_cat)
  fst_def G H := by ext; simp [fst_def]; congr
  snd_def G H := by ext; simp [snd_def]; congr

@[simp] lemma lift_hom (f : G ⟶ H₁) (g : G ⟶ H₂) : (lift f g).hom = lift f.hom g.hom := rfl
@[simp] lemma fst_hom (G H : Grp_ C) : (fst G H).hom = fst G.X H.X := rfl
@[simp] lemma snd_hom (G H : Grp_ C) : (snd G H).hom = snd G.X H.X := rfl

namespace Hom
variable [BraidedCategory C] [IsCommMon H.X]

/-- A commutative group object is a group object in the category of group objects. -/
instance : Grp_Class H where
  one :=
    .mk M.one (by simp [Mon_.one_eq_one]) (by simp [toUnit_unique (ρ_ (𝟙_ C)).hom (λ_ (𝟙_ C)).hom])
  mul := .mk M.mul (by simp [toUnit_unique (ρ_ (𝟙_ C)).hom (λ_ (𝟙_ C)).hom]) <| by
    simp
    sorry
  one_mul' := by ext; simp
  mul_one' := by ext; simp
  mul_assoc' := by ext; simp

instance {G : C} [Grp_Class G] [IsCommMon G] : IsMon_Hom (ι : G ⟶ G) where
  one_hom := by simp only [one_eq_one]; exact inv_one
  mul_hom := by simp [Grp_Class.mul_inv_rev]

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

@[simp] lemma hom_inv (f : G ⟶ H) : f⁻¹.hom = f.hom⁻¹ := rfl

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

instance instCommGroup : CommGroup (G ⟶ H) := inferInstance

end Grp_.Hom

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

end yoneda

/-!
# Group objects form a cartesian-monoidal category
-/

open CategoryTheory MonoidalCategory Limits CartesianMonoidalCategory Mon_Class

attribute [local simp] leftUnitor_hom rightUnitor_hom

namespace CategoryTheory

universe u v v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] [CartesianMonoidalCategory C]

@[simps]
def homToProd {X Y Z : C} : (Z ⟶ X ⊗ Y) ≃ (Z ⟶ X) × (Z ⟶ Y) where
  toFun f := ⟨f ≫ fst _ _, f ≫ snd _ _⟩
  invFun f := lift f.1 f.2
  left_inv _ := by simp
  right_inv _ := by simp

namespace Functor
variable {D E : Type*} [Category D] [Category E] [CartesianMonoidalCategory E]

noncomputable def tensorObjComp (F G : D ⥤ C) (H : C ⥤ E) [PreservesFiniteProducts H] :
    (F ⊗ G) ⋙ H ≅ (F ⋙ H) ⊗ (G ⋙ H) :=
  NatIso.ofComponents (fun X ↦ prodComparisonIso H (F.obj X) (G.obj X)) fun {X Y} f ↦ by
    dsimp
    ext <;> simp [← Functor.map_comp]

protected def RepresentableBy.tensorObj {F : Cᵒᵖ ⥤ Type v} {G : Cᵒᵖ ⥤ Type v} {X Y : C}
    (h₁ : F.RepresentableBy X) (h₂ : G.RepresentableBy Y) : (F ⊗ G).RepresentableBy (X ⊗ Y) where
  homEquiv {Z} := homToProd.trans (Equiv.prodCongr h₁.homEquiv h₂.homEquiv)
  homEquiv_comp {Z W} f g := by
    refine Prod.ext ?_ ?_
    · refine (h₁.homEquiv_comp _ _).trans ?_
      simp
      change
        F.map f.op (F.map g.op (h₁.homEquiv (fst X Y))) = F.map f.op (h₁.homEquiv (g ≫ fst X Y))
      simp [h₁.homEquiv_comp]
    · refine (h₂.homEquiv_comp _ _).trans ?_
      simp
      change
        G.map f.op (G.map g.op (h₂.homEquiv (snd X Y))) = G.map f.op (h₂.homEquiv (g ≫ snd X Y))
      simp [h₂.homEquiv_comp]

end CategoryTheory.Functor

section

variable {C : Type*} [Category C] [CartesianMonoidalCategory C]
    {X Y : C} [Grp_Class X] [Grp_Class Y]

@[simps]
instance : Grp_Class <| 𝟙_ C where
  one := 𝟙 _
  mul := toUnit _
  inv := 𝟙 _


/- noncomputable instance : Grp_Class <| X ⊗ Y where
  inv := ι ⊗ ι
  left_inv' := by
    ext
    · simp
  right_inv' := _ -/

noncomputable instance Grp_Class_tensorObj : Grp_Class <| X ⊗ Y :=
  .ofRepresentableBy _ (yonedaGrpObj X ⊗ yonedaGrpObj Y) <| .ofIso
    ((yonedaGrpObjRepresentableBy _).tensorObj (yonedaGrpObjRepresentableBy _))
      (Functor.tensorObjComp _ _ _).symm

@[simp]
lemma prodObj : (Grp_.mk' (X ⊗ Y)).X = X ⊗ Y := rfl

-- TODO: complain on Zulip
@[ext]
lemma prodExt {Z : C} {f g : Z ⟶ (Grp_.mk' (X ⊗ Y)).X} (h₁ : f ≫ fst _ _ = g ≫ fst _ _)
    (h₂ : f ≫ snd _ _ = g ≫ snd _ _) : f = g := by
  simp at f g
  sorry

lemma prodOne : η[X ⊗ Y] = lift η η := by
  ext <;> simp <;> sorry

lemma prodInv : ι[X ⊗ Y] = ι[X] ⊗ ι[Y] := sorry

noncomputable instance : CartesianMonoidalCategory <| Grp_ C :=
  .ofChosenFiniteProducts {
    cone.pt := Grp_.mk' (𝟙_ C)
    cone.π.app := isEmptyElim
    cone.π.naturality := isEmptyElim
    isLimit.lift s := {
      hom := toUnit _
      one_hom := toUnit_unique _ _
      mul_hom := toUnit_unique _ _
    }
    isLimit.uniq s m h := by ext; exact toUnit_unique _ _
  } fun X Y ↦ {
    cone.pt := .mk' (X.X ⊗ Y.X)
    cone.π.app := by
      rintro (_|_)
      · refine ⟨fst X.X Y.X, ?_, ?_⟩
        · simp [Grp_.mk']
          sorry
        simp [Grp_.mk']
        sorry
      sorry
    cone.π.naturality := sorry
    isLimit.lift s := {
      hom := by
        dsimp
        sorry
      one_hom := sorry
      mul_hom := sorry
    }
    isLimit.fac := sorry
    isLimit.uniq := sorry
  }

end
