import Mathlib.Algebra.FreeAbelianGroup.Finsupp
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.RingTheory.Finiteness.Finsupp

namespace AddMonoidAlgebra
variable {ι R S : Type*} [Finite ι] [Semiring R] [Semiring S] [Module R S] [Module.Finite R S]

instance moduleFinite : Module.Finite R S[ι] := .finsupp

end AddMonoidAlgebra

namespace MonoidAlgebra
variable {ι R S : Type*} [Finite ι] [Semiring R] [Semiring S] [Module R S] [Module.Finite R S]

instance moduleFinite : Module.Finite R (MonoidAlgebra S ι) := .finsupp

end MonoidAlgebra

namespace FreeAbelianGroup
variable {σ : Type*} [Finite σ]

instance : Module.Finite ℤ (FreeAbelianGroup σ) :=
  .of_surjective _ (FreeAbelianGroup.equivFinsupp σ).toIntLinearEquiv.symm.surjective

instance : AddMonoid.FG (FreeAbelianGroup σ) := by
  rw [← AddGroup.fg_iff_addMonoid_fg, ← Module.Finite.iff_addGroup_fg]; infer_instance

end FreeAbelianGroup
