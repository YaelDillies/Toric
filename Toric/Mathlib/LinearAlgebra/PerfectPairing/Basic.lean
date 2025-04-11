import Mathlib.LinearAlgebra.PerfectPairing.Basic

namespace PerfectPairing

-- Make `PerfectPairing` a class
attribute [class] PerfectPairing

-- Use scalar product notation for the bilinear map in perfect pairings
scoped[PerfectPairing] notation "⟪" x ", " y "⟫_" R:max => PerfectPairing.toLin (R := R) inferInstance x y

variable {R N M : Type*}
variable [CommRing R] [AddCommGroup N] [AddCommGroup M] [Module R N] [Module R M]

instance instFlip [inst : PerfectPairing R N M] : PerfectPairing R M N :=
  inst.flip

example [PerfectPairing R N M] (x : N) (y : M) : ⟪x,y⟫_R = ⟪y,x⟫_R := rfl

end PerfectPairing
