import Mathlib.Algebra.FreeAbelianGroup.Finsupp
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.LinearAlgebra.Finsupp.VectorSpace

namespace FreeAbelianGroup

instance {σ : Type*} : Module.Free ℤ (FreeAbelianGroup σ) where
  exists_basis := ⟨σ, ⟨(FreeAbelianGroup.equivFinsupp _).toIntLinearEquiv⟩⟩

end FreeAbelianGroup

namespace AddMonoidAlgebra
variable {ι R S : Type*} [Semiring R] [Semiring S] [Module R S] [Module.Free R S]

instance moduleFree : Module.Free R S[ι] := .finsupp ..

end AddMonoidAlgebra

namespace MonoidAlgebra
variable {ι R S : Type*} [Semiring R] [Semiring S] [Module R S] [Module.Free R S]

instance moduleFree : Module.Free R (MonoidAlgebra S ι) := .finsupp ..

end MonoidAlgebra
