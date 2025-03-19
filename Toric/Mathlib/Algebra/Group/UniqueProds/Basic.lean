import Mathlib.Algebra.Group.UniqueProds.Basic
import Mathlib.GroupTheory.FreeAbelianGroupFinsupp

--Maybe the correct place to put this is in a new Mathlib file to avoid
--making too large import changes!

instance {σ : Type*} : UniqueSums (FreeAbelianGroup σ) :=
  (AddEquiv.uniqueSums_iff (FreeAbelianGroup.equivFinsupp σ)).mpr inferInstance
