import Mathlib
import Toric.Mathlib.GroupTheory.MonoidLocalization.Basic

variable {M : Type*} [AddCommMonoid M] [AddMonoid.FG M] [IsCancelAdd M] {hM : AddMonoid.IsTorsionFree M}

lemma affine_monoid_imp_lattice_embedding :
    ∃ (n : ℕ) (f : M →+ FreeAbelianGroup (Fin n)), Function.Injective f :=
  let G := AddLocalization (⊤ : AddSubmonoid M)
  have hG : Module.Free ℤ G := by {
    sorry
  }
  sorry
