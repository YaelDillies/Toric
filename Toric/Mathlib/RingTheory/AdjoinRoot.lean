import Mathlib.RingTheory.AdjoinRoot

open TensorProduct

namespace AdjoinRoot

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
variable (p : Polynomial S)

-- TODO : find better name
noncomputable def map (f : S →+* T) : AdjoinRoot p →+* AdjoinRoot (.map f p) :=
  lift ((algebraMap T _).comp f) (root (.map f p)) (by
    rw [← Polynomial.eval₂_map, ← Polynomial.aeval_def, aeval_eq, mk_self])

def tensorAlgEquiv :
    letI := Algebra.TensorProduct.rightAlgebra (R := R) (A := T) (B := S)
    T ⊗[R] AdjoinRoot p ≃ₐ[T] AdjoinRoot (R := T ⊗[R] S) (.map (algebraMap S (T ⊗[R] S)) p) where
  toFun := Algebra.TensorProduct.lift (Algebra.algHom T T _)
      (AdjoinRoot.map)
      _
  invFun := sorry
  left_inv := sorry
  right_inv := sorry
  map_mul' := sorry
  map_add' := sorry
  commutes' := sorry

end AdjoinRoot
