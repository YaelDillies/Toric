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

open CategoryTheory Mon_Class MonoidalCategory --Category

variable {C : Type*} [Category C] [ChosenFiniteProducts C] (M : C) [Mon_Class M]
/--
An action of a monoid object `M` on an object `S` is the data of map
`smul : M ⊗ S ⟶ S` that satisfies "the right commutative diagrams":
-/
class Action_Class (S : C) where
  /--The action map-/
  smul : M ⊗ S ⟶ S-/
  mul_smul' : (𝟙 M ⊗ smul) ≫ smul
    = (α_ M M S).inv ≫ (μ ⊗ (𝟙 S)) ≫ smul := by aesop_cat
  one_smul' : (λ_ S).inv ≫ η ▷ S ≫ smul = 𝟙 S := by aesop_cat

namespace Action_Class

@[inherit_doc] notation "γ" => Action_Class.smul
--@[inherit_doc] notation "γ["M";"S"]" => Action_Class.smul M S

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


--TODO(Paul-Lez): finish local progress on defining the category and add it below.
/--The category of objects acted on by a monoid object `M`-/
structure ActedBy where
  private mk::
  carrier : C
  [action : Action_Class M carrier]

instance : CoeOut (ActedBy M) C where
  coe A := A.carrier

instance (A : ActedBy M) : Action_Class M A := A.action

attribute [instance] ActedBy.action

initialize_simps_projections SemiRingCat (-action)

def trivialAction (S : C) : Action_Class M S where
  smul := (ChosenFiniteProducts.toUnit M ▷ S) ≫ (λ_ S).hom
  mul_smul' := by
    --This is painful
    rw [← Category.assoc, ←Category.assoc (α_ M M S).inv, ←Category.assoc ((α_ M M S).inv ≫ (μ ⊗ 𝟙 S : (M ⊗ M) ⊗ S ⟶ M ⊗ S)), Iso.cancel_iso_hom_right, assoc, tensorHom_id,
      ←comp_whiskerRight, ChosenFiniteProducts.comp_toUnit, associator_inv_naturality_right]
    have : μ ▷ S = (μ[M] ⊗ 𝟙 S)  := rfl
    rw [←this, ←assoc]
    sorry
  one_smul' := by
    --In an ideal world `aesop_cat` would already solve this
    rw [Iso.inv_comp_eq_id, ←Iso.comp_inv_eq_id]
    aesop_cat

def selfAction : Action_Class M M where
  smul := γ
  mul_smul' := sorry --This is probably aesop_cat
  one_smul' := sorry --same

end Mon_
