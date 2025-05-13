import Mathlib.LinearAlgebra.LinearIndependent.Defs

/-!
# TODO

Make statement of `LinearIndependent.not_mem_smul_span` match its name
-/

open Set Submodule

variable {ι R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
  {v : ι → M} {s : Set ι} {i : ι}

lemma LinearIndepOn.eq_zero_of_smul_mem_span (hv : LinearIndepOn R v s) (hi : i ∈ s) (a : R)
    (ha : a • v i ∈ span R (v '' (s \ {i}))) : a = 0 :=
  hv.not_smul_mem_span ⟨i, hi⟩ _ <| by
    simpa [← Function.comp_def, image_comp, image_diff Subtype.val_injective]

variable [Nontrivial R]

lemma LinearIndependent.not_mem_span (hv : LinearIndependent R v) (i : ι) :
    v i ∉ span R (v '' {i}ᶜ) := fun hi ↦
  one_ne_zero <| hv.not_smul_mem_span i 1 <| by simpa [Set.compl_eq_univ_diff] using hi

lemma LinearIndepOn.not_mem_span (hv : LinearIndepOn R v s) (hi : i ∈ s) :
    v i ∉ span R (v '' (s \ {i})) := fun hi' ↦
  one_ne_zero <| hv.eq_zero_of_smul_mem_span hi 1 <| by  simpa [Set.compl_eq_univ_diff] using hi'

lemma LinearIndepOn.not_mem_span_of_insert (hv : LinearIndepOn R v (insert i s)) (hi : i ∉ s) :
    v i ∉ span R (v '' s) := by simpa [hi] using hv.not_mem_span <| mem_insert ..
