import Toric.GroupScheme.GroupScheme
import Mathlib.CategoryTheory.Monoidal.Grp_
import Toric.Mathlib.CategoryTheory.Monoidal.Grp_
import Toric.Mathlib.CategoryTheory.Monoidal.Yoneda

open CategoryTheory AlgebraicGeometry Opposite

attribute [local instance] ChosenFiniteProducts.ofFiniteProducts

noncomputable instance (σ : Type*) : Grp_Class (AlgebraicGeometry.TorusInt σ) :=
  Grp_Class.ofRepresentableBy _ (Scheme.Γ ⋙ forget₂ _ CommMonCat ⋙ CommMonCat.units ⋙
      CommGrp.coyonedaRight.obj (op σ) ⋙ forget₂ _ Grp) (TorusInt.representableBy σ)

instance (σ : Type*) : IsCommMon (TorusInt σ) :=
  IsCommMon.ofRepresentableBy _ (Scheme.Γ ⋙ forget₂ _ CommMonCat ⋙ CommMonCat.units ⋙
      CommGrp.coyonedaRight.obj (op σ) ⋙ forget₂ _ CommMonCat) (TorusInt.representableBy σ)
