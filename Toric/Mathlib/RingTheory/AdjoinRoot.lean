import Mathlib.RingTheory.AdjoinRoot
import Toric.Mathlib.RingTheory.TensorProduct.Basic

open TensorProduct

noncomputable section

namespace AdjoinRoot

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
variable (p : Polynomial S)

-- TODO : find better name
def map (f : S →+* T) : AdjoinRoot p →+* AdjoinRoot (.map f p) :=
  lift ((algebraMap T _).comp f) (root (.map f p)) (by
    rw [← Polynomial.eval₂_map, ← Polynomial.aeval_def, aeval_eq, mk_self])

def mapAlgHom (f : S →ₐ[R] T) : AdjoinRoot p →ₐ[R] AdjoinRoot (p.map f.toRingHom) where
  __ := map p f.toRingHom
  commutes' r := by
    simp [map]
    sorry

def tensorAlgEquiv :
    letI := Algebra.TensorProduct.rightAlgebra (R := R) (A := T) (B := S)
    T ⊗[R] AdjoinRoot p ≃ₐ[T] AdjoinRoot (R := T ⊗[R] S) (.map (algebraMap S (T ⊗[R] S)) p) where
  __ := Algebra.TensorProduct.lift (Algebra.algHom T T _) (mapAlgHom _ _) fun t y ↦ .all ..
  invFun := lift
    (Algebra.TensorProduct.lTensor _ ((Algebra.ofId S (AdjoinRoot p)).restrictScalars R)).toRingHom
    (1 ⊗ₜ (root _))
    sorry
  left_inv := sorry
  right_inv := sorry

end AdjoinRoot

end
