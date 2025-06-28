import Mathlib.Algebra.Group.Equiv.Defs
import Mathlib.Algebra.Group.Hom.Basic
import Mathlib.Algebra.Group.Units.Hom

namespace MonoidHom
variable {G M : Type*} [Group G] [CommMonoid M]

@[simp] lemma toHomUnits_mul (f g : G →* M) : (f * g).toHomUnits = f.toHomUnits * g.toHomUnits := by
  ext; rfl

/-- `MonoidHom.toHomUnits` as a `MulEquiv`. -/
def toHomUnitsMulEquiv : (G →* M) ≃* (G →* Mˣ) where
  toFun := toHomUnits
  invFun f := (Units.coeHom _).comp f
  map_mul' := by simp

end MonoidHom
