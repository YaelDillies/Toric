import Mathlib.RingTheory.Bialgebra.MonoidAlgebra
import Toric.Mathlib.Algebra.MonoidAlgebra.Basic
import Toric.Mathlib.LinearAlgebra.TensorProduct.Basic
import Toric.Mathlib.RingTheory.Bialgebra.Equiv

open Coalgebra

variable {R A M N O : Type*}

namespace MonoidAlgebra
variable [CommSemiring R] [Semiring A] [Bialgebra R A] [Monoid M] [Monoid N] [Monoid O]

variable (R A) in
/-- Isomorphic monoids have isomorphic monoid algebras. -/
@[simps!]
def domCongrBialgHom (e : M ≃* N) : MonoidAlgebra A M ≃ₐc[R] MonoidAlgebra A N :=
  .ofAlgEquiv (domCongr R A e) (by ext; simp) (by ext; simp [TensorProduct.map_map])

-- TODO: Generalise to `MonoidAlgebra A M →ₐc[R] MonoidAlgebra A N` under `Bialgebra R A`
variable (R) in
/-- If `f : M → N` is a monoid hom, then `MonoidAlgebra.mapDomain f` is a bialgebra hom between
their monoid algebras. -/
@[simps]
noncomputable def mapDomainBialgHom (f : M →* N) : MonoidAlgebra R M →ₐc[R] MonoidAlgebra R N where
  __ := mapDomainAlgHom R R f
  map_smul' m x := by simp
  counit_comp := by ext; simp
  map_comp_comul := by ext; simp

@[simp] lemma mapDomainBialgHom_id : mapDomainBialgHom R (.id M) = .id _ _ := by ext; simp

@[simp]
lemma mapDomainBialgHom_mapDomainBialgHom (f : N →* O) (g : M →* N) (x : MonoidAlgebra R M) :
    mapDomainBialgHom R (f.comp g) x = mapDomainBialgHom R f (mapDomainBialgHom R g x) := by
  ext; simp

@[simp]
lemma mapDomainBialgHom_comp (f : N →* O) (g : M →* N) : mapDomainBialgHom R (f.comp g) =
    (mapDomainBialgHom R f).comp (mapDomainBialgHom R g) := by ext; simp

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

-- TODO: Generalise to `A[M] →ₐc[R] A[N]` under `Bialgebra R A`
variable (R) in
/-- If `f : M → N` is a monoid hom, then `AddMonoidAlgebra.mapDomain f` is a bialgebra hom between
their monoid algebras. -/
@[simps]
noncomputable def mapDomainBialgHom (f : M →+ N) : R[M] →ₐc[R] R[N] where
  __ := mapDomainAlgHom R R f
  map_smul' m x := by simp
  counit_comp := by ext; simp
  map_comp_comul := by ext; simp

@[simp] lemma mapDomainBialgHom_id : mapDomainBialgHom R (.id M) = .id _ _ := by ext; simp

@[simp]
lemma mapDomainBialgHom_comp (f : N →+ O) (g : M →+ N) : mapDomainBialgHom R (f.comp g) =
    (mapDomainBialgHom R f).comp (mapDomainBialgHom R g) := by ext; simp

variable (M) in
/-- The trivial monoid algebra is isomorphic to the base ring. -/
noncomputable def bialgEquivOfSubsingleton [Subsingleton M] : R[M] ≃ₐc[R] R where
  __ := Bialgebra.counitBialgHom ..
  invFun := algebraMap _ _
  left_inv r := by
    show (Algebra.ofId _ _).comp (Bialgebra.counitAlgHom R _) r = AlgHom.id R _ r
    congr 1
    ext g : 2
    simp [Subsingleton.elim g 1, AddMonoidAlgebra.one_def]
  right_inv := (Bialgebra.counitAlgHom R R[M]).commutes

end AddMonoidAlgebra
