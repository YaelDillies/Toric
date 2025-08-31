import Mathlib.Algebra.Algebra.Tower
import Mathlib.Algebra.MonoidAlgebra.Basic

namespace MonoidAlgebra
variable {R S M : Type*} [CommMonoid M] [CommSemiring R] [CommSemiring S] [Algebra R S]

/--
If `S` is an `R`-algebra, then `MonoidAlgebra S σ` is a `MonoidAlgebra R σ` algebra.

Warning: This produces a diamond for
`Algebra (MonoidAlgebra R σ) (MonoidAlgebra (MonoidAlgebra S σ) σ)`. That's why it is not a
global instance.
-/
noncomputable abbrev algebraMonoidAlgebra : Algebra (MonoidAlgebra R M) (MonoidAlgebra S M) :=
  (mapRangeRingHom M (algebraMap R S)).toAlgebra

attribute [local instance] algebraMonoidAlgebra

@[simp]
lemma algebraMap_def :
    algebraMap (MonoidAlgebra R M) (MonoidAlgebra S M) = mapRangeRingHom M (algebraMap R S) :=
  rfl

instance {T : Type*} [CommSemiring T] [Algebra R T] [Algebra S T] [IsScalarTower R S T] :
    IsScalarTower R (MonoidAlgebra S M) (MonoidAlgebra T M) :=
  .of_algebraMap_eq' (mapRangeAlgHom _ (IsScalarTower.toAlgHom R S T)).comp_algebraMap.symm

end MonoidAlgebra
