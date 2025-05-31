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

namespace Grp_

@[simp] lemma mk'_X (G : C) [Grp_Class G] : (mk' G).X = G := rfl

namespace Hom

instance instOne : One (G ⟶ H) := inferInstanceAs <| One (G.toMon_ ⟶ H.toMon_)

lemma hom_one : (1 : (G ⟶ H)).hom = 1 := rfl

variable [BraidedCategory C] [IsCommMon H.X]

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
