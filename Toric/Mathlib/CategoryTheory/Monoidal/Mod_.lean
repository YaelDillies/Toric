import Mathlib.CategoryTheory.Monoidal.Mod_

section Mod_Class

open CategoryTheory Mon_Class MonoidalCategory
variable {C : Type*} [Category C] [MonoidalCategory C]
variable (M : C) [Mon_Class M]

/-- An action of a monoid object `M` on an object `X` is the data of a map `smul : M ⊗ X ⟶ X` that
satisfies unitality and associativity with multiplication.
See `MulAction` for the non-categorical version. -/
class Mod_Class (X : C) where
  /-- The action map -/
  smul : M ⊗ X ⟶ X
  /-- The identity acts trivially. -/
  one_smul (X) : η ▷ X ≫ smul = (λ_ X).hom := by aesop_cat
  /-- The action map is compatible with multiplication. -/
  mul_smul (X) : μ ▷ X ≫ smul = (α_ M M X).hom ≫ M ◁ smul ≫ smul := by aesop_cat

attribute [reassoc (attr := simp)] Mod_Class.mul_smul Mod_Class.one_smul

@[inherit_doc] scoped[Mon_Class] notation "γ" => Mod_Class.smul
@[inherit_doc] scoped[Mon_Class] notation "γ["X"]" => Mod_Class.smul (X := X)

namespace Mod_Class

open Mon_Class

theorem assoc_flip (X : C) [Mod_Class M X] : M ◁ γ ≫ γ[X] = (α_ M M X).inv ≫ μ[M] ▷ X ≫ γ := by
  simp

/-- The action of a monoid object on itself. -/
-- See note [reducible non instances]
abbrev regular : Mod_Class M M where smul := μ

instance {A : Mon_ C} (M : Mod_ A) : Mod_Class A.X M.X where
  smul := M.act
  one_smul := M.one_act
  mul_smul := M.assoc

end Mod_Class

/-- Construct an object of `Mod_ (Mon_.mk' M)` from an object `X : C` and a
`Mod_Class M X` instance. -/
@[simps]
def Mod_.mk' (X : C) [Mod_Class M X] : Mod_ (.mk' M) where
  X := X
  act := γ[M]

end Mod_Class
