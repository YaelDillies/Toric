import Mathlib.RingTheory.Bialgebra.MonoidAlgebra
import Toric.Mathlib.RingTheory.Bialgebra.Convolution

suppress_compilation

open Coalgebra

variable {R A G M N : Type*}

namespace MonoidAlgebra
variable [CommSemiring R]

section Semiring
variable [Semiring A] [Bialgebra R A] [Monoid M] [Monoid N]

/-- A `R`-algebra homomorphism from `MonoidAlgebra R M` is uniquely defined by its
values on the functions `single a 1`. -/
lemma bialgHom_ext ⦃φ₁ φ₂ : MonoidAlgebra R M →ₐc[R] A⦄
    (h : ∀ x, φ₁ (single x 1) = φ₂ (single x 1)) : φ₁ = φ₂ :=
  BialgHom.coe_algHom_injective <| algHom_ext h

-- The priority must be `high`.
/-- See note [partially-applied ext lemmas]. -/
@[ext high]
lemma bialgHom_ext' ⦃φ₁ φ₂ : MonoidAlgebra R M →ₐc[R] A⦄
    (h : (φ₁ : MonoidAlgebra R M →* A).comp (of R M) = .comp φ₂ (of R M)) : φ₁ = φ₂ :=
  bialgHom_ext fun x ↦ congr($h x)

@[simp] lemma counit_domCongr (e : M ≃* N) (x : MonoidAlgebra A M) :
    counit (R := R) (domCongr R A e x) = counit x := by
  induction x using MonoidAlgebra.induction_linear <;> simp [*]

variable (R A) in
/-- Isomorphic monoids have isomorphic monoid algebras. -/
@[simps!]
def domCongrBialgHom (e : M ≃* N) : MonoidAlgebra A M ≃ₐc[R] MonoidAlgebra A N :=
  .ofAlgEquiv (domCongr R A e) (by ext; simp) <| by
    apply AlgHom.toLinearMap_injective
    ext
    simp [TensorProduct.map_map, TensorProduct.AlgebraTensorModule.map_eq]

variable (M) in
/-- The trivial monoid algebra is isomorphic to the base ring. -/
noncomputable def bialgEquivOfSubsingleton [Subsingleton M] : MonoidAlgebra R M ≃ₐc[R] R where
  __ := Bialgebra.counitBialgHom ..
  invFun := algebraMap _ _
  left_inv r := by
    show (Algebra.ofId _ _).comp (Bialgebra.counitAlgHom R _) r = AlgHom.id R _ r
    congr 1
    ext g : 2
    simp [Subsingleton.elim g 1]
  right_inv := (Bialgebra.counitAlgHom R (MonoidAlgebra R M)).commutes

end Semiring

section CommSemiring
variable [CommSemiring A]

section Algebra
variable [Algebra R A] [Monoid M]

variable (R M A) in
/-- `MonoidAlgebra.lift` as a `MulEquiv`. -/
def liftMulEquiv : (M →* A) ≃* (MonoidAlgebra R M →ₐ[R] A) where
  __ := lift R M A
  map_mul' f g := by ext; simp

@[simp]
lemma convMul_algHom_single (f g : MonoidAlgebra R M →ₐ[R] A) (x : M) :
    (f * g) (single x 1) = f (single x 1) * g (single x 1) := by
  simp [← AlgHom.toLinearMap_apply, AlgHom.toLinearMap_mul]

end Algebra

@[simp]
lemma convMul_bialgHom_single [Bialgebra R A] [CommMonoid M] (f g : MonoidAlgebra R M →ₐc[R] A)
    (x : M) : (f * g) (single x 1) = f (single x 1) * g (single x 1) := by
  simp [← BialgHom.toCoalgHom_apply, ← CoalgHom.coe_toLinearMap, ← CoalgHom.toLinearMap_eq_coe,
    -LinearMap.coe_coe, BialgHom.toLinearMap_mul]

end CommSemiring

section CommMonoid
variable [CommMonoid M] [CommMonoid N]

@[simp]
lemma mapDomainBialgHom_mul (f g : M →* N) :
    mapDomainBialgHom R (f * g) = mapDomainBialgHom R f * mapDomainBialgHom R g := by
  ext x : 2; simp

end CommMonoid
end MonoidAlgebra

namespace AddMonoidAlgebra
variable [CommSemiring R]

section Semiring
variable [Semiring A] [Bialgebra R A]

section AddMonoid
variable [AddMonoid M] [AddMonoid N]

/-- A `R`-algebra homomorphism from `R[M]` is uniquely defined by its values on the functions
`single a 1`. -/
lemma bialgHom_ext ⦃φ₁ φ₂ : R[M] →ₐc[R] A⦄ (h : ∀ x, φ₁ (single x 1) = φ₂ (single x 1)) : φ₁ = φ₂ :=
  BialgHom.coe_algHom_injective <| algHom_ext h

-- The priority must be `high`.
/-- See note [partially-applied ext lemmas]. -/
@[ext high]
lemma bialgHom_ext' ⦃φ₁ φ₂ : R[M] →ₐc[R] A⦄
    (h : (φ₁ : R[M] →* A).comp (of R M) = .comp φ₂ (of R M)) : φ₁ = φ₂ :=
  bialgHom_ext fun x ↦ congr($h x)

@[simp] lemma counit_domCongr (e : M ≃+ N) (x : A[M]) :
    counit (R := R) (domCongr R A e x) = counit x := by
  induction x using MonoidAlgebra.induction_linear <;> simp [*]

variable (R A) in
/-- Isomorphic monoids have isomorphic monoid algebras. -/
@[simps!]
def domCongrBialgHom (e : M ≃+ N) : A[M] ≃ₐc[R] A[N] :=
  .ofAlgEquiv (domCongr R A e) (by ext; simp) <| by
    apply AlgHom.toLinearMap_injective
    ext
    simp [TensorProduct.map_map, TensorProduct.AlgebraTensorModule.map_eq]

variable (M) in
/-- The trivial monoid algebra is isomorphic to the base ring. -/
noncomputable def bialgEquivOfSubsingleton [Subsingleton M] : R[M] ≃ₐc[R] R where
  __ := Bialgebra.counitBialgHom ..
  invFun := algebraMap _ _
  left_inv r := by
    show (Algebra.ofId _ _).comp (Bialgebra.counitAlgHom R _) r = AlgHom.id R _ r
    congr 1
    ext g : 3
    simp [Subsingleton.elim g 0]
  right_inv := (Bialgebra.counitAlgHom R R[M]).commutes

end AddMonoid
end Semiring

section CommSemiring
variable [CommSemiring A]

@[simp]
lemma convMul_algHom_single [Algebra R A] [AddMonoid M] (f g : R[M] →ₐ[R] A) (x : M) :
    (f * g) (single x 1) = f (single x 1) * g (single x 1) := by
  simp [← AlgHom.toLinearMap_apply, AlgHom.toLinearMap_mul]

@[simp]
lemma convMul_bialgHom_single [Bialgebra R A] [AddCommMonoid M] (f g : R[M] →ₐc[R] A) (x : M) :
    (f * g) (single x 1) = f (single x 1) * g (single x 1) := by
  simp [← BialgHom.toCoalgHom_apply, ← CoalgHom.coe_toLinearMap, ← CoalgHom.toLinearMap_eq_coe,
    -LinearMap.coe_coe, BialgHom.toLinearMap_mul]

end CommSemiring

section AddCommMonoid
variable [AddCommMonoid M] [AddCommMonoid N]

@[simp]
lemma mapDomainBialgHom_add (f g : M →+ N) :
    mapDomainBialgHom R (f + g) = mapDomainBialgHom R f * mapDomainBialgHom R g :=
  MonoidAlgebra.mapDomainBialgHom_mul f.toMultiplicative g.toMultiplicative

end AddCommMonoid
end AddMonoidAlgebra
