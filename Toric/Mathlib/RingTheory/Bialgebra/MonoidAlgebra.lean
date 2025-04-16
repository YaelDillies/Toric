import Mathlib.RingTheory.Bialgebra.Hom
import Mathlib.RingTheory.Bialgebra.MonoidAlgebra
import Toric.Hopf.GroupLike

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

namespace MonoidAlgebra

open Bialgebra Coalgebra

variable (R : Type*) {A M : Type*}

variable [CommSemiring R] [Monoid M] [Semiring A] [Bialgebra R A]

/--
A multiplicative map from a monoid `M` into the group of grouplike elements of `A`
lifts to an `R`-algebra map from `MonoidAlgebra R M` to `A`.
-/
@[simps!]
noncomputable def grouplike_lift_algHom (φ : M →* GroupLike R A) :
    MonoidAlgebra R M →ₐ[R] A := MonoidAlgebra.lift R M A {
  toFun x := (φ x).1
  map_one' := by rw [φ.map_one]; rfl
  map_mul' a b := by rw [φ.map_mul]; rfl }

/--
A multiplicative map from a monoid `M` into the group of grouplike elements of `A`
lifts to an `R`-bialgebra map from `MonoidAlgebra R M` to `A`.
-/
@[simps!]
noncomputable def grouplike_lift_bialgHom (hinj : Function.Injective (algebraMap R A))
    (φ : M →* GroupLike R A) : MonoidAlgebra R M →ₐc[R] A :=
  {grouplike_lift_algHom R φ with
    counit_comp := by
      ext x
      dsimp
      simp only [MonoidAlgebra.liftNC_single, AddMonoidHom.coe_coe, map_one, one_mul,
        MonoidAlgebra.counit_single, CommSemiring.counit_apply]
      exact IsGroupLikeElem.counit_eq_one hinj (φ x).2,
    map_comp_comul := by
      ext x
      dsimp
      simp only [MonoidAlgebra.comul_single, CommSemiring.comul_apply, TensorProduct.map_tmul,
        MonoidAlgebra.lsingle_apply, LinearMap.coe_mk, AddHom.coe_mk, grouplike_lift_algHom_apply,
        MonoidAlgebra.liftNC_single, AddMonoidHom.coe_coe, map_one, one_mul]
      exact (φ x).2.comul_eq_tmul_self.symm,
    map_smul' := fun _ _ ↦ by dsimp [grouplike_lift_algHom]; simp only [map_smul]}

section CommSemiring
variable [CommSemiring R] [CommSemiring A] [Bialgebra R A]

variable (A) in
/--
The `R`-algebra map from the monoid algebra on the group-like elements of `A` to `A`.
-/
@[simps!]
noncomputable def lift_isGroupLikeElem_algHom :
    MonoidAlgebra R (GroupLike R A) →ₐ[R] A :=
  MonoidAlgebra.grouplike_lift_algHom R (MonoidHom.id _)

/--
The `R`-bialgebra map from the monoid algebra on the group-like elements of `A` to `A`.
-/
@[simps!]
noncomputable def lift_isGroupLikeElem_bialgHom (hinj : Function.Injective (algebraMap R A)) :
    MonoidAlgebra R (GroupLike R A) →ₐc[R] A :=
  MonoidAlgebra.grouplike_lift_bialgHom R hinj (MonoidHom.id _)

end CommSemiring

end MonoidAlgebra
