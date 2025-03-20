/-
Copyright (c) 2025 Yaël Dillies, Michał Mrugała, Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Michał Mrugała, Andrew Yang
-/
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Monoidal.Grp_
import Toric.Mathlib.CategoryTheory.Monoidal.Mon_

/-!
# Yoneda embedding of `Grp_ C`

We show that group objects are exactly those whose yoneda presheaf is a presheaf of groups,
by constructing the yoneda embedding `Grp_ C ⥤ Cᵒᵖ ⥤ GrpCat.{v}` and
showing that it is fully faithful and its (essential) image is the representable functors.

-/

open CategoryTheory Mon_Class MonoidalCategory ChosenFiniteProducts Opposite

section Yoneda

universe w v u

variable {C : Type*} [Category.{v} C] [ChosenFiniteProducts C]
variable (X : C)

/-- If `X` represents a presheaf of groups, then `X` is a group object. -/
def Grp_Class.ofRepresentableBy (F : Cᵒᵖ ⥤ Grp.{w}) (α : (F ⋙ forget _).RepresentableBy X) :
    Grp_Class X where
  __ := Mon_Class.ofRepresentableBy X (F ⋙ (forget₂ Grp MonCat)) α
  inv := α.homEquiv.symm (α.homEquiv (𝟙 _))⁻¹
  left_inv' := by
    change lift (α.homEquiv.symm (α.homEquiv (𝟙 X))⁻¹) (𝟙 X) ≫
      α.homEquiv.symm (α.homEquiv (fst X X) * α.homEquiv (snd X X)) =
        toUnit X ≫ α.homEquiv.symm 1
    apply α.homEquiv.injective
    simp only [α.homEquiv_comp, Equiv.apply_symm_apply]
    simp only [Functor.comp_map, ConcreteCategory.forget_map_eq_coe, map_one, map_mul]
    simp only [← ConcreteCategory.forget_map_eq_coe, ← Functor.comp_map, ← α.homEquiv_comp]
    simp [← Functor.comp_obj]
  right_inv' := by
    change lift (𝟙 X) (α.homEquiv.symm (α.homEquiv (𝟙 X))⁻¹) ≫
      α.homEquiv.symm (α.homEquiv (fst X X) * α.homEquiv (snd X X)) =
        toUnit X ≫ α.homEquiv.symm 1
    apply α.homEquiv.injective
    simp only [α.homEquiv_comp, Equiv.apply_symm_apply]
    simp only [Functor.comp_map, ConcreteCategory.forget_map_eq_coe, map_one, map_mul]
    simp only [← ConcreteCategory.forget_map_eq_coe, ← Functor.comp_map, ← α.homEquiv_comp]
    simp [← Functor.comp_obj]

attribute [local instance] monoidOfMon_Class

instance Grp_Class.instInv [Grp_Class X] (Y : C) : Inv (Y ⟶ X) where
  inv := (· ≫ ι)

/-- If `X` is a group object, then `Hom(Y, X)` has a group structure. -/
@[reducible] def groupOfGrp_Class [Grp_Class X] (Y : C) : Group (Y ⟶ X) where
  __ := monoidOfMon_Class X Y
  div_eq_mul_inv _ _ := rfl
  zpow := zpowRec
  inv_mul_cancel f := by
    change lift (f ≫ ι) _ ≫ μ = toUnit Y ≫ η
    rw [← comp_toUnit f, Category.assoc, ← Grp_Class.left_inv _, comp_lift_assoc, Category.comp_id]

attribute [local instance] groupOfGrp_Class

/- If `X` is a group object, then `Hom(-, X)` is a presheaf of groups. -/
@[simps]
def yonedaGrpObj [Grp_Class X] : Cᵒᵖ ⥤ Grp.{v} where
  obj Y := .of (unop Y ⟶ X)
  map φ := Grp.ofHom ((yonedaMonObj X).map φ).hom

/-- If `X` is a group object, then `Hom(-, X)` as a presheaf of group is represented by `X`. -/
def yonedaGrpObjRepresentableBy [Grp_Class X] : (yonedaGrpObj X ⋙ forget _).RepresentableBy X :=
  Functor.representableByEquiv.symm (Iso.refl _)

lemma Grp_ClassOfRepresentableBy_yonedaGrpObjRepresentableBy [Grp_Class X] :
    Grp_Class.ofRepresentableBy X _ (yonedaGrpObjRepresentableBy X) = ‹_› := by
  ext
  show lift (fst X X) (snd X X) ≫ μ = μ
  rw [lift_fst_snd, Category.id_comp]

/-- If `X` represents a presheaf of groups `F`, then `Hom(-, X)` is isomorphic to `F` as
a presheaf of groups. -/
@[simps!]
def yonedaGrpObjGrp_ClassOfRepresentableBy
    (F : Cᵒᵖ ⥤ Grp.{v}) (α : (F ⋙ forget _).RepresentableBy X) :
    letI := Grp_Class.ofRepresentableBy X F α
    yonedaGrpObj X ≅ F :=
  letI := Grp_Class.ofRepresentableBy X F α
  NatIso.ofComponents (fun Y ↦ MulEquiv.toGrpIso
    { toEquiv := α.homEquiv
      map_mul' :=
  ((yonedaMonObjMon_Class.ofRepresentableBy X (F ⋙ forget₂ Grp MonCat) α).hom.app Y).hom.map_mul})
      (fun φ ↦ Grp.hom_ext (MonoidHom.ext (α.homEquiv_comp φ.unop)))

/-- The yoneda embedding of `Grp_C` into presheaves of groups. -/
@[simps]
def yonedaGrp : Grp_ C ⥤ Cᵒᵖ ⥤ Grp.{v} where
  obj X := yonedaGrpObj X.X
  map {X₁ X₂} ψ :=
  { app Y := Grp.ofHom ((yonedaMon.map ψ).app Y).hom }

@[reassoc]
lemma yonedaGrp_naturality {X₁ X₂ : C} [Grp_Class X₁] [Grp_Class X₂]
    (α : yonedaGrpObj X₁ ⟶ yonedaGrpObj X₂) {Y₁ Y₂ : C} (f : Y₁ ⟶ Y₂) (g : Y₂ ⟶ X₁) :
      α.app _ (f ≫ g) = f ≫ α.app _ g := congr($(α.naturality f.op) g)

/-- The yoneda embedding for `Grp_C` is fully faithful. -/
noncomputable def yonedaGrpFullyFaithful : yonedaGrp (C := C).FullyFaithful where
  preimage {X₁ X₂} α := yonedaMon.preimage (whiskerRight α (forget₂ Grp MonCat))
  map_preimage {X₁ X₂} α := by
    ext X:3
    exact congr(($(yonedaMon.map_preimage (whiskerRight α (forget₂ Grp MonCat))).app X).hom)
  preimage_map := yonedaMon.preimage_map

instance : yonedaGrp (C := C).Full := yonedaGrpFullyFaithful.full
instance : yonedaGrp (C := C).Faithful := yonedaGrpFullyFaithful.faithful

lemma essImage_yonedaGrp :
    yonedaGrp (C := C).essImage = (· ⋙ forget _) ⁻¹' setOf Functor.IsRepresentable := by
  ext F
  constructor
  · rintro ⟨X, ⟨α⟩⟩
    exact ⟨X.X, ⟨Functor.representableByEquiv.symm (isoWhiskerRight α (forget _))⟩⟩
  · rintro ⟨X, ⟨e⟩⟩
    letI := Grp_Class.ofRepresentableBy X F e
    exact ⟨Grp_.mk' X, ⟨yonedaGrpObjGrp_ClassOfRepresentableBy X F e⟩⟩

variable {X} {G : C} [Grp_Class G]

-- TODO (Michał): doc string
def yonedaGrpObjRepresentableByOverMkSnd :
    ((Over.forget X).op ⋙ yonedaGrpObj G ⋙ forget Grp).RepresentableBy (.mk (snd G X)) where
  homEquiv {Y} := show (Y ⟶ Over.mk (snd G X)) ≃ (Y.left ⟶ G) from {
      toFun f := f.left ≫ fst _ _
      invFun f := Over.homMk (lift f Y.hom)
      left_inv f := by ext; simp; ext <;> simp; simpa using f.w.symm
      right_inv f := by simp
    }
  homEquiv_comp {Y Z} f g := by dsimp; erw [Equiv.coe_fn_mk, Equiv.coe_fn_mk]; simp

variable [Limits.HasPullbacks C]

attribute [local instance] Over.chosenFiniteProducts

noncomputable instance : Grp_Class <| Over.mk <| snd G X :=
  .ofRepresentableBy _ ((Over.forget _).op ⋙ yonedaGrpObj G) yonedaGrpObjRepresentableByOverMkSnd

end Yoneda

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

section

variable {C : Type*} [Category C] [ChosenFiniteProducts C] {G : C}

instance [Grp_Class G] [IsCommMon G] : IsCommMon (Grp_.mk' G).X := ‹_›

end

end

open Limits

namespace CategoryTheory.Functor
universe v₁ v₂ u₁ u₂
variable {C : Type u₁} [Category.{v₁} C] [ChosenFiniteProducts.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D] [ChosenFiniteProducts.{v₂} D]
variable (F : C ⥤ D) [PreservesFiniteProducts F]

attribute [local instance] monoidalOfChosenFiniteProducts

protected instance Faithful.mapGrp [F.Faithful] : F.mapGrp.Faithful where
  map_injective {_X _Y} _f _g hfg := F.mapMon.map_injective hfg

protected instance Full.mapGrp [F.Full] [F.Faithful] : F.mapGrp.Full where
  map_surjective := F.mapMon.map_surjective

end CategoryTheory.Functor

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Equivalence
variable {C : Type u₁} [Category.{v₁} C] [ChosenFiniteProducts C]
variable {D : Type u₂} [Category.{v₂} D] [ChosenFiniteProducts D]

noncomputable def mapGrp (e : C ≌ D) [e.functor.Monoidal] [e.inverse.Monoidal]
    [NatTrans.IsMonoidal e.unit] [NatTrans.IsMonoidal e.counit] :
    Grp_ C ≌ Grp_ D where
  functor := e.functor.mapGrp
  inverse := e.inverse.mapGrp
  unitIso := by
    refine NatIso.ofComponents (fun X ↦ Grp_.mkIso (e.unitIso.app _) ?_ ?_) fun {X Y} f ↦ ?_
    · dsimp
      simp
      have := NatTrans.IsMonoidal.unit (τ := e.unit)
      change X.one ≫ e.unit.app X.X = _
      sorry
    · simp
      sorry
    · ext
      simp
  counitIso := by
    refine NatIso.ofComponents (fun X ↦ Grp_.mkIso (e.counitIso.app _) ?_ ?_) fun {X Y} f ↦ ?_
    · simp
      sorry
    · simp
      sorry
    · ext
      simp
  functor_unitIso_comp X := by ext; simp

end CategoryTheory.Equivalence
