import Mathlib.RingTheory.Bialgebra.MonoidAlgebra
import Toric.Mathlib.LinearAlgebra.TensorProduct.Basic
import Toric.Mathlib.RingTheory.Bialgebra.Equiv
import Toric.Mathlib.Algebra.MonoidAlgebra.Defs

suppress_compilation

section

open Coalgebra

variable {R A M N O : Type*}

namespace MonoidAlgebra
variable [CommSemiring R] [Semiring A] [Bialgebra R A] [Monoid M] [Monoid N] [Monoid O]

variable (R A) in
/-- Isomorphic monoids have isomorphic monoid algebras. -/
@[simps!]
def domCongrBialgHom (e : M ≃* N) : MonoidAlgebra A M ≃ₐc[R] MonoidAlgebra A N :=
  .ofAlgEquiv (domCongr R A e) (by ext; simp) (by ext; simp [TensorProduct.map_map])

variable (M) in
/-- The trivial monoid algebra is isomorphic to the base ring. -/
noncomputable def bialgEquivOfSubsingleton [Subsingleton M] : MonoidAlgebra R M ≃ₐc[R] R where
  __ := Bialgebra.counitBialgHom ..
  invFun := algebraMap _ _
  left_inv r := by
    show (Algebra.ofId _ _).comp (Bialgebra.counitAlgHom R _) r = AlgHom.id R _ r
    congr 1
    ext g : 2
    simp [Subsingleton.elim g 1, MonoidAlgebra.one_def]
  right_inv := (Bialgebra.counitAlgHom R (MonoidAlgebra R M)).commutes

end MonoidAlgebra

namespace AddMonoidAlgebra
variable [CommSemiring R] [Semiring A] [Bialgebra R A] [AddMonoid M] [AddMonoid N] [AddMonoid O]

variable (R A) in
/-- Isomorphic monoids have isomorphic monoid algebras. -/
@[simps!]
def domCongrBialgHom (e : M ≃+ N) : A[M] ≃ₐc[R] A[N] :=
  .ofAlgEquiv (domCongr R A e) (by ext; simp) (by ext; simp [TensorProduct.map_map])

variable (M) in
/-- The trivial monoid algebra is isomorphic to the base ring. -/
noncomputable def bialgEquivOfSubsingleton [Subsingleton M] : R[M] ≃ₐc[R] R where
  __ := Bialgebra.counitBialgHom ..
  invFun := algebraMap _ _
  left_inv r := by
    show (Algebra.ofId _ _).comp (Bialgebra.counitAlgHom R _) r = AlgHom.id R _ r
    congr 1
    ext g : 3
    simp [Subsingleton.elim g 0, AddMonoidAlgebra.one_def]
  right_inv := (Bialgebra.counitAlgHom R R[M]).commutes

end AddMonoidAlgebra

end
