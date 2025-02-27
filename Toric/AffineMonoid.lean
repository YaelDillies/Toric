import Mathlib.GroupTheory.FreeAbelianGroup
import Mathlib.GroupTheory.Torsion
import Mathlib.LinearAlgebra.FreeModule.Basic
import Toric.Mathlib.GroupTheory.MonoidLocalization.Basic

variable {M : Type*} [AddCommMonoid M] [AddMonoid.FG M] [IsCancelAdd M]

lemma affine_monoid_imp_lattice_embedding (hM : AddMonoid.IsTorsionFree M) :
    ∃ (n : ℕ) (f : M →+ FreeAbelianGroup (Fin n)), Function.Injective f :=
  let G := AddLocalization (⊤ : AddSubmonoid M)
  have hG : Module.Free ℤ G := by {
    sorry
  }
  sorry
