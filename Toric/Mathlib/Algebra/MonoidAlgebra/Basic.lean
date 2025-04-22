import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.LinearAlgebra.DirectSum.Finsupp
import Mathlib.LinearAlgebra.Finsupp.VectorSpace
import Mathlib.LinearAlgebra.TensorProduct.Basis

open TensorProduct

namespace MonoidAlgebra

variable (R R' M : Type*) [CommSemiring R] [CommSemiring R'] [Monoid M] [Algebra R R']

noncomputable def baseChangeAlgEquiv :
    MonoidAlgebra R' M ≃ₐ[R'] R' ⊗[R] MonoidAlgebra R M := by
  set f : MonoidAlgebra R' M →ₐ[R'] R' ⊗[R] MonoidAlgebra R M :=
    MonoidAlgebra.lift R' M (R' ⊗[R] MonoidAlgebra R M)
    {toFun m := 1 ⊗ₜ[R] of R M m,
     map_mul' m n := by rw [(of R M).map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one],
     map_one' := by rw [Algebra.TensorProduct.one_def, (of R M).map_one]
     }
  set b : Basis M R' (MonoidAlgebra R' M) := Finsupp.basisSingleOne
  set b' : Basis M R' (R' ⊗[R] MonoidAlgebra R M) := Basis.baseChange R' Finsupp.basisSingleOne
  set g := Basis.equiv b b' (Equiv.refl _)
  have eq : ⇑f = ⇑g := by
    ext
    apply LinearMap.congr_fun (f := f.toLinearMap)
    refine b.ext (fun m ↦ ?_)
    dsimp [b, b', f, g]
    simp only [Basis.equiv_apply, Equiv.refl_apply, Basis.baseChange_apply, b, g, b', f]
    rw [MonoidAlgebra.lift_apply]
    erw [Finsupp.coe_basisSingleOne]
    simp only [zero_smul, Finsupp.sum_single_index, one_smul, b, g, b', f]
    rfl
  refine AlgEquiv.ofBijective f ?_
  rw [eq]
  exact LinearEquiv.bijective g

@[simp]
lemma baseChangeAlgEquiv_apply_of (m : M) :
    baseChangeAlgEquiv R R' M (of R' M m) = 1 ⊗ₜ[R] (of R M m) := by
  dsimp [baseChangeAlgEquiv]
  rw [lift_apply]
  simp only [MonoidHom.coe_mk, OneHom.coe_mk, zero_smul, Finsupp.sum_single_index, one_smul]

end MonoidAlgebra
