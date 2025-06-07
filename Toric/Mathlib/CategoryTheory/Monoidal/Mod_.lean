import Mathlib.CategoryTheory.Monoidal.Mod_

open CategoryTheory
open scoped Mon_Class

@[inherit_doc] scoped[Mon_Class] notation "γ["M' ", " X'"]" => Mod_Class.smul (M := M') (X := X')

namespace Mod_Class
variable {C : Type*} [Category C] [MonoidalCategory C]

attribute [local instance] regular in
@[simp] lemma smul_eq_mul (M : C) [Mon_Class M] : γ[M, M] = μ[M] := rfl

end Mod_Class
