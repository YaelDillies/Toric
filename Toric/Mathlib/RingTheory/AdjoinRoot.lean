import Mathlib.RingTheory.AdjoinRoot
import Toric.Mathlib.RingTheory.TensorProduct.Basic

open TensorProduct

noncomputable section


namespace AdjoinRoot

section
variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
variable {p : Polynomial S}

-- TODO : replace liftHom by this
def liftAlgHom (i : S →ₐ[R] T) (x : T) (h : p.eval₂ i x = 0) : AdjoinRoot p →ₐ[R] T where
  __ := lift i.toRingHom _ h
  commutes' r := by
    simp [lift_of h, AdjoinRoot.algebraMap_eq']

@[simp]
theorem coe_liftAlgHom (i : S →ₐ[R] T) (x : T) (h : p.eval₂ i x = 0) :
    (liftAlgHom i x h : AdjoinRoot p →+* T) = lift i.toRingHom _ h :=
  rfl

@[simp]
theorem liftAlgHom_of {s : S} {i : S →ₐ[R] T} {x : T} {h : p.eval₂ i x = 0} :
    liftAlgHom i x h (of p s) = i s := by simp [liftAlgHom]

@[simp]
theorem liftAlgHom_root {i : S →ₐ[R] T} {x : T} {h : p.eval₂ i x = 0} :
    liftAlgHom i x h (root p) = x := by simp [liftAlgHom]

variable (p) in
-- TODO : find better name
def map (f : S →+* T) : AdjoinRoot p →+* AdjoinRoot (.map f p) :=
  lift ((algebraMap T _).comp f) (root (.map f p)) (by
    rw [← Polynomial.eval₂_map, ← Polynomial.aeval_def, aeval_eq, mk_self])

@[simp]
theorem map_of {s : S} {f : S →+* T} : map p f ((of p) s) = f s := by simp [map]

@[simp]
theorem map_root {f : S →+* T} : map p f (root p) = root (p.map f) := by simp [map]

variable (p) in
def mapAlgHom (f : S →ₐ[R] T) : AdjoinRoot p →ₐ[R] AdjoinRoot (p.map f.toRingHom) where
  __ := map p f.toRingHom
  commutes' r := by
    simp [map, AdjoinRoot.algebraMap_eq']

@[simp]
theorem mapAlgHom_of {s : S} {f : S →ₐ[R] T} : mapAlgHom p f ((of p) s) = f s := by simp [mapAlgHom]

@[simp]
theorem mapAlgHom_root {f : S →ₐ[R] T} : mapAlgHom p f (root p) = root (p.map f.toRingHom) := by
  simp [mapAlgHom]

theorem algHom_ext' {f g : AdjoinRoot p →ₐ[R] T} (hAlg :
    f.comp ((Algebra.ofId S _).restrictScalars R) = g.comp ((Algebra.ofId S _).restrictScalars R))
    (hRoot : f (root p) = g (root p)) : f = g := by
  apply Ideal.Quotient.algHom_ext
  ext x
  · show f (AdjoinRoot.mk _ _) = g (AdjoinRoot.mk _ _)
    simp
    exact congr($(hAlg) x)
  show f (AdjoinRoot.mk _ _) = g (AdjoinRoot.mk _ _)
  simpa

variable (p) in
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
    apply algHom_ext'
    · ext s
      simp [Algebra.ofId_apply, AdjoinRoot.algebraMap_eq']
      erw [mapAlgHom_of]
      rfl
    simp
    erw [mapAlgHom_root]
    rfl)
  sorry

end
end AdjoinRoot

end
