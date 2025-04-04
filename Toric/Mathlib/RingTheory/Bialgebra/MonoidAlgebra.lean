import Mathlib.RingTheory.Bialgebra.Hom
import Mathlib.RingTheory.Bialgebra.MonoidAlgebra

open Coalgebra

namespace MonoidAlgebra
variable {R A M N : Type*} [CommSemiring R] [Monoid M] [Monoid N]

/-- If `f : M → N` is a monoid hom, then `MonoidAlgebra.mapDomain f` is a bialgebra hom between
their monoid algebras. -/
@[simps]
noncomputable def mapDomainBialgHom (f : M →* N) : MonoidAlgebra R M →ₐc[R] MonoidAlgebra R N where
  __ := mapDomainAlgHom R R f
  map_smul' m x := by simp
  counit_comp := by ext; simp
  map_comp_comul := by ext; simp

end MonoidAlgebra
