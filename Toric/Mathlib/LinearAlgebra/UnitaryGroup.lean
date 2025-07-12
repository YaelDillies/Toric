import Mathlib.LinearAlgebra.UnitaryGroup

namespace Matrix
variable {R : Type*} [CommRing R]

lemma mem_specialOrthogonalGroup_fin_two_iff {M : Matrix (Fin 2) (Fin 2) R} :
    M ∈ Matrix.specialOrthogonalGroup (Fin 2) R ↔
      M 0 0 = M 1 1 ∧ M 0 1 = - M 1 0 ∧ M 0 0 ^ 2 + M 0 1 ^ 2 = 1 := by
  obtain ⟨a, b, c, d, rfl⟩ : ∃ a b c d, M = !![a, b; c, d] :=
    ⟨M 0 0, M 0 1, M 1 0, M 1 1, by ext i j; fin_cases i, j <;> rfl⟩
  trans ((a * a + b * b = 1 ∧ a * c + b * d = 0) ∧
    c * a + d * b = 0 ∧ c * c + d * d = 1) ∧ a * d - b * c = 1
  · simp [Matrix.mem_specialOrthogonalGroup_iff, Matrix.mem_orthogonalGroup_iff,
      ← Matrix.ext_iff, Fin.forall_fin_succ, Matrix.vecHead, Matrix.vecTail]
  dsimp
  refine ⟨?_, ?_⟩
  · rintro ⟨⟨⟨h₀, h₁⟩, -, h₂⟩, h₃⟩
    refine ⟨?_, ?_, ?_⟩
    · linear_combination - a * h₂ + c * h₁ + d * h₃
    · linear_combination - c * h₀ + a * h₁ - b * h₃
    · linear_combination h₀
  · rintro ⟨rfl, rfl, H⟩
    ring_nf at H ⊢
    tauto

end Matrix
