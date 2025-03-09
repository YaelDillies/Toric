/-
Copyright (c) 2025 Paul Lezeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Lezeau
-/
import Toric.Mathlib.CategoryTheory.Monoidal.Mon_
import Mathlib.Algebra.Category.Grp.Adjunctions
import Mathlib.Algebra.Category.Ring.Adjunctions
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.CategoryTheory.Adjunction.Opposites
import Mathlib.CategoryTheory.Monoidal.Yoneda

open CategoryTheory Mon_Class MonoidalCategory

variable {C : Type*} [Category C] [ChosenFiniteProducts C] (M : C) [Mon_Class M]
/--
An action of a monoid object `M` on an object `S` is the data of map
`smul : M ⊗ S ⟶ S` that satisfies "the right commutative diagrams":
-/
class Action_Class (S : C) where
  /--The action map-/
  smul : M ⊗ S ⟶ S
  mul_smul' : (𝟙 M ⊗ smul) ≫ smul
    = (α_ M M S).inv ≫ (μ ⊗ (𝟙 S)) ≫ smul := by aesop_cat
  one_smul' : (λ_ S).inv ≫ η ▷ S ≫ smul = 𝟙 S := by aesop_cat

namespace Action_Class

@[inherit_doc] notation "γ" => Action_Class.smul
@[inherit_doc] notation "γ["M";"S"]" => Action_Class.smul M S

/- The simp attribute is reserved for the unprimed versions. -/
attribute [reassoc] mul_smul' one_smul'

@[reassoc (attr := simp)]
lemma mul_smul (S : C) [Action_Class M S] : (𝟙 M ⊗ γ) ≫ γ
    = (α_ M M S).inv ≫
      (μ ⊗ (𝟙 S) : (M ⊗ M) ⊗ S ⟶ M ⊗ S) ≫ γ := mul_smul'


--TODO(Paul-Lez): fix `γ` notation
@[reassoc (attr := simp)]
lemma one_smul (S : C) [Action_Class M S] :
    (λ_ S).inv ≫ η ▷ S ≫ (γ : M ⊗ S ⟶ S) = 𝟙 S := one_smul'

structure ActedBy where
  carrier : C
  action : Action_Class M carrier

instance : CoeOut (ActedBy M) C where
  coe A := A.carrier

instance (A : ActedBy M) : Action_Class M A := A.action

#check Iso.inv_comp_eq_id
#check CategoryTheory.Category
-- #check MonoidalCategory.whiskerRight_comp

open Category


-- Do we need an additional axiom for this (e.g. a morphism from `S` to `𝟙_ C`?)
def trivialAction (S : C) : Action_Class M S where
  smul := (ChosenFiniteProducts.toUnit M ▷ S) ≫ (λ_ S).hom
  mul_smul' := by
    rw [← Category.assoc, ←Category.assoc (α_ M M S).inv, ←Category.assoc ((α_ M M S).inv ≫ (μ ⊗ 𝟙 S : (M ⊗ M) ⊗ S ⟶ M ⊗ S)), Iso.cancel_iso_hom_right, assoc, tensorHom_id,
      ←comp_whiskerRight, ChosenFiniteProducts.comp_toUnit, associator_inv_naturality_right]
    have :   μ ▷ S = (μ[M] ⊗ 𝟙 S)  := rfl
    rw [←this, ←assoc]
    simp?
    --rw [←whiskerRight_comp]
    --aesop_cat
    congr
    --have : (ChosenFiniteProducts.toUnit M ⊗ 𝟙 S) ≫ (λ_ S).hom
    -- ←assoc (α_ M M S).hom, ←associator_naturality
    rw [(α_ M M S).eq_inv_comp, ←leftUnitor_naturality]

  one_smul' := by
    --This should be `aesop_cat`...
    rw [Iso.inv_comp_eq_id, ←Iso.comp_inv_eq_id]
    sorry --aesop_cat

instance (S : C) : Inhabited (Action_Class M S) where
  default := trivialAction M S

namespace ActedBy

variable {M}

@[ext]
structure hom (A B : ActedBy M) where
  toHom : (A : C) ⟶ B
  equivariant : (𝟙 M ⊗ toHom) ≫ γ = γ ≫ toHom := by aesop_cat

def identity (A : ActedBy M) : hom A A where
  toHom := 𝟙 (A : C)

def comp' {A B C : ActedBy M} (f : hom A B) (g : hom B C) :
  hom A C where
  toHom := f.toHom ≫ g.toHom
  equivariant := by
    sorry

instance : Category (ActedBy M) where
  Hom A B := hom A B
  id A := { toHom := 𝟙 (A : C) }
  comp f g := ActedBy.comp'  f g
  id_comp := by aesop_cat
  comp_id := sorry
  assoc := sorry

end ActedBy

end Mon_
