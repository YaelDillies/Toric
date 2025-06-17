import Mathlib.RingTheory.AdjoinRoot
import Toric.Mathlib.RingTheory.TensorProduct.Basic

open TensorProduct

noncomputable section


namespace AdjoinRoot

section
variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
variable (p : Polynomial S)

-- TODO : replace liftHom by this
variable {p} in
def liftAlgHom (i : S →ₐ[R] T) (x : T) (h : Polynomial.eval₂ i x p = 0) : AdjoinRoot p →ₐ[R] T where
  __ := lift i.toRingHom _ h
  commutes' r := by
    simp [lift_of h, AdjoinRoot.algebraMap_eq']

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
    T ⊗[R] AdjoinRoot p ≃ₐ[T] AdjoinRoot (R := T ⊗[R] S) (.map (algebraMap S (T ⊗[R] S)) p) :=
  .ofAlgHom (Algebra.TensorProduct.lift (Algebra.algHom T T _) (mapAlgHom _ _) fun t y ↦ .all ..)
  (liftAlgHom (Algebra.TensorProduct.map (AlgHom.id T T)
    (((Algebra.ofId S (AdjoinRoot p))).restrictScalars R))
    (1 ⊗ₜ (root _)) <| by
    trans Algebra.TensorProduct.includeRight (Polynomial.aeval (root p) p)
    · rw [Polynomial.eval₂_map, Polynomial.aeval_def, ← AlgHom.coe_toRingHom, Polynomial.hom_eval₂]
      rfl
    · simp)
  (by
    -- ext lemma missing here!
    sorry)
  sorry

end
end AdjoinRoot

end
