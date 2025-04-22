import Mathlib.RingTheory.Bialgebra.Hom
import Mathlib.RingTheory.Bialgebra.MonoidAlgebra
import Mathlib.RingTheory.Bialgebra.Equiv
import Toric.Mathlib.Algebra.MonoidAlgebra.Basic


open Coalgebra

variable {R A M N O : Type*}

namespace MonoidAlgebra
variable [CommSemiring R] [Monoid M] [Monoid N] [Monoid O]

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

end MonoidAlgebra

namespace AddMonoidAlgebra
variable [CommSemiring R] [AddMonoid M] [AddMonoid N] [AddMonoid O]

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

end AddMonoidAlgebra

open TensorProduct

namespace MonoidAlgebra

variable {R R' M : Type*} [CommSemiring R] [CommSemiring R'] [Monoid M] [Algebra R R']

lemma baseChangeAlgEquiv_symm_counit (x : R' ⊗[R] MonoidAlgebra R M) :
    Coalgebra.counit (R := R') ((baseChangeAlgEquiv R R' M).symm x) =
    Algebra.TensorProduct.rid R R' R' (Algebra.TensorProduct.map (AlgHom.id R' R')
    (Bialgebra.counitAlgHom R (MonoidAlgebra R M)) x) := sorry

end MonoidAlgebra
