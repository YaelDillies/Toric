/-
Copyright (c) 2025 Michał Mrugała, Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michał Mrugała, Andrew Yang
-/
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Monoidal.Yoneda
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Toric.Mathlib.CategoryTheory.Monoidal.Grp_

/-!
# Yoneda embedding of `Grp_ C`

We show that group objects are exactly those whose yoneda presheaf is a presheaf of groups,
by constructing the yoneda embedding `Grp_ C ⥤ Cᵒᵖ ⥤ GrpCat.{v}` and
showing that it is fully faithful and its (essential) image is the representable functors.

-/

open CategoryTheory ChosenFiniteProducts MonoidalCategory Mon_Class Opposite

universe w v u

variable {C : Type*} [Category.{v} C] [ChosenFiniteProducts C]
variable (X : C)

section Grp_

variable (F : Cᵒᵖ ⥤ Grp)

/-- If `X` represents a presheaf of groups, then `X` is a group object. -/
def Grp_Class.ofRepresentableBy (F : Cᵒᵖ ⥤ Grp.{w}) (α : (F ⋙ forget _).RepresentableBy X) :
    Grp_Class X where
  __ := Mon_ClassOfRepresentableBy X (F ⋙ (forget₂ Grp MonCat)) α
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
  obj Y := Grp.of (unop Y ⟶ X)
  map φ := Grp.ofHom ((yonedaMonObj X).map φ).hom

/-- If `X` is a group object, then `Hom(-, X)` as a presheaf of group is represented by `X`. -/
def yonedaGrpObjRepresentableBy [Grp_Class X] : (yonedaGrpObj X ⋙ forget _).RepresentableBy X :=
  Functor.representableByEquiv.symm (Iso.refl _)

lemma Grp_ClassOfRepresentableBy_yonedaGrpObjRepresentableBy [Grp_Class X] :
    Grp_Class.ofRepresentableBy X _ (yonedaGrpObjRepresentableBy X) = ‹_› := by
  ext
  · show toUnit _ ≫ η = η
    rw [toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
  · show lift (fst X X) (snd X X) ≫ μ = μ
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
  ((yonedaMonObjMon_ClassOfRepresentableBy X (F ⋙ forget₂ Grp MonCat) α).hom.app Y).hom.map_mul})
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

end Grp_
