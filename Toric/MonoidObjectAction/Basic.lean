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


/-
TODO(Paul-Lez):
- Do Yoneda stuff.
- Start upstreaming to Mathlib.
-/

open CategoryTheory Mon_Class MonoidalCategory

variable {C : Type*} [Category C] [ChosenFiniteProducts C] (M : C) [Mon_Class M]
/--
An action of a monoid object `M` on an object `S` is the data of map
`smul : M ⊗ S ⟶ S` that satisfies "the right commutative diagrams":
-/
class Action_Class (S : C) where
  /-- The action map -/
  smul : M ⊗ S ⟶ S
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

def trivialAction (S : C) : Action_Class M S where
  smul := ChosenFiniteProducts.snd M S

def selfAction : Action_Class M M where
  smul := μ

end Action_Class
