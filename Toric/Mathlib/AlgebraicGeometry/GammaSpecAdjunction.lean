import Mathlib.AlgebraicGeometry.GammaSpecAdjunction

namespace AlgebraicGeometry.Spec

open CategoryTheory

@[simp]
lemma map_eq_id {R : CommRingCat} {ϕ : R ⟶ R} : Spec.map ϕ = 𝟙 (Spec R) ↔ ϕ = 𝟙 R := by
  simp [← map_inj]
