import Mathlib.RingTheory.Bialgebra.MonoidAlgebra
import Toric.Mathlib.LinearAlgebra.TensorProduct.Basic
import Toric.Mathlib.RingTheory.Bialgebra.Equiv
import Toric.Mathlib.RingTheory.Bialgebra.Hom
import Toric.Mathlib.RingTheory.Bialgebra.Convolution

suppress_compilation

open Coalgebra

variable {R A M N O : Type*}

namespace MonoidAlgebra
variable [CommSemiring R] [Semiring A] [Bialgebra R A] [Monoid M] [Monoid N] [Monoid O]

/-- A `k`-algebra homomorphism from `MonoidAlgebra R M` is uniquely defined by its
values on the functions `single a 1`. -/
lemma bialgHom_ext ⦃φ₁ φ₂ : MonoidAlgebra R M →ₐc[R] A⦄
    (h : ∀ x, φ₁ (single x 1) = φ₂ (single x 1)) : φ₁ = φ₂ :=
  BialgHom.toAlgHom_injective <| algHom_ext h

-- The priority must be `high`.
/-- See note [partially-applied ext lemmas]. -/
@[ext high]
lemma bialgHom_ext' ⦃φ₁ φ₂ : MonoidAlgebra R M →ₐc[R] A⦄
    (h : (φ₁ : MonoidAlgebra R M →* A).comp (of R M) = .comp φ₂ (of R M)) : φ₁ = φ₂ :=
  bialgHom_ext fun x ↦ congr($h x)

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

namespace MonoidAlgebra
variable [CommSemiring R]

section
variable  [Semiring A] [Bialgebra R A]

@[simp]
lemma convMul_linear_single (f g : MonoidAlgebra R M →ₗ[R] A) (x : M) :
    (f * g) (single x 1) = f (single x 1) * g (single x 1) := by simp

end

section

variable [CommSemiring A] [Bialgebra R A]

section
variable [Monoid M]

@[simp]
lemma convMul_AlgHom_single (f g : MonoidAlgebra R M →ₐ[R] A) (x : M) :
    (f * g) (single x 1) = f (single x 1) * g (single x 1) := by
  simp [← AlgHom.toLinearMap_apply, AlgHom.toLinearMap_mul]

end

section
variable [CommMonoid M]

@[simp]
lemma convMul_BialgHom_single (f g : MonoidAlgebra R M →ₐc[R] A) (x : M) :
    (f * g) (single x 1) = f (single x 1) * g (single x 1) := by
  simp [← BialgHom.toLinearMap_apply, -CoalgHom.toLinearMap_eq_coe, BialgHom.toLinearMap_mul]

end
end

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
