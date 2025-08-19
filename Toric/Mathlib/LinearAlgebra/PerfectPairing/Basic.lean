import Mathlib.LinearAlgebra.PerfectPairing.Basic

open Function Module

namespace LinearMap
variable {R K M N M' N' : Type*} [AddCommGroup M] [AddCommGroup N]
  [AddCommGroup M'] [AddCommGroup N']

variable [CommRing R] [Module R M] [Module R N] (p : M →ₗ[R] N →ₗ[R] R) {x : M} {y : N}
variable [Module R M'] [Module R N'] [p.IsPerfPair]

instance IsPerfPair.compl₁₂ (eM : M' ≃ₗ[R] M) (eN : N' ≃ₗ[R] N) :
    (p.compl₁₂ eM eN : M' →ₗ[R] N' →ₗ[R] R).IsPerfPair :=
  ⟨((LinearEquiv.congrLeft R R eN).symm.bijective.comp
    (IsPerfPair.bijective_left p)).comp eM.bijective,
    ((LinearEquiv.congrLeft R R eM).symm.bijective.comp
    (IsPerfPair.bijective_right p)).comp eN.bijective⟩

lemma IsPerfPair.congr (eM : M' ≃ₗ[R] M) (eN : N' ≃ₗ[R] N) (q : M' →ₗ[R] N' →ₗ[R] R)
    (H : q.compl₁₂ eM.symm eN.symm = p) : q.IsPerfPair := by
  obtain rfl : q = p.compl₁₂ eM eN := by subst H; ext; simp
  infer_instance

lemma IsPerfPair.of_bijective (p : M →ₗ[R] N →ₗ[R] R) [IsReflexive R N] (h : Bijective p) :
    IsPerfPair p :=
  inferInstanceAs ((LinearMap.id (R := R) (M := Dual R N)).compl₁₂
    (LinearEquiv.ofBijective p h : M →ₗ[R] N →ₗ[R] R)
    (LinearEquiv.refl R N : N →ₗ[R] N)).IsPerfPair

end LinearMap
