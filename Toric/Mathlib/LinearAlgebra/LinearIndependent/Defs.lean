import Mathlib.LinearAlgebra.LinearIndependent.Defs

alias ⟨LinearIndependent.fintypeLinearCombination_injective, _⟩ :=
  Fintype.linearIndependent_iff_injective

section Module
variable {K V ι : Type*}
variable [DivisionRing K] [AddCommGroup V] [Module K V]
variable {v : ι → V} {s t : Set ι} {x y : V}

open Submodule

lemma linearIndepOn_iff_not_mem_span :
    LinearIndepOn K v s ↔ ∀ i ∈ s, v i ∉ span K (v '' (s \ {i})) := by
  rw [LinearIndepOn, linearIndependent_iff_not_mem_span, ← Function.comp_def]
  simp_rw [Set.image_comp]
  simp [Set.image_diff Subtype.val_injective]

end Module
