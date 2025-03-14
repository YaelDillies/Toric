import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.LinearAlgebra.FreeModule.PID
import Toric.Mathlib.Algebra.NoZeroSMulDivisors.Defs

variable {G : Type*}

@[simp]
lemma Module.free_int_iff_isAddTorsionFree [AddCommGroup G] [Module.Finite ℤ G] :
    Module.Free ℤ G ↔ IsAddTorsionFree G :=
  Module.free_iff_noZeroSMulDivisors.trans noZeroSMulDivisors_int_iff_isAddTorsionFree
