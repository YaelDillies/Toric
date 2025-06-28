import Mathlib.RingTheory.AdjoinRoot
import Toric.Mathlib.Algebra.Algebra.Equiv
import Toric.Mathlib.RingTheory.FiniteType

open TensorProduct

noncomputable section

namespace AdjoinRoot
variable {R S T U : Type*} [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
  [CommRing U] [Algebra R U] {p : Polynomial S}

instance [Algebra.FiniteType R S] : Algebra.FiniteType R (AdjoinRoot p) := by
  unfold AdjoinRoot; infer_instance

section
variable {q : Polynomial T} {u : Polynomial U}

variable (R p) in
/-- Embedding of the original ring `R` into `AdjoinRoot f`. -/
def ofAlgHom : S →ₐ[R] AdjoinRoot p where
  __ := of p
  commutes' r := by simp [AdjoinRoot.algebraMap_eq']

@[simp]
lemma toRingHom_ofAlgHom : ofAlgHom R p = of p := rfl

@[simp]
lemma ofAlgHom_apply (s : S) : ofAlgHom R p s = of p s := rfl

@[ext]
lemma algHom_ext' {f g : AdjoinRoot p →ₐ[R] T} (hAlg :
    f.comp (ofAlgHom R p) = g.comp (ofAlgHom R p))
    (hRoot : f (root p) = g (root p)) : f = g := by
  apply Ideal.Quotient.algHom_ext
  ext x
  · show f (AdjoinRoot.mk _ _) = g (AdjoinRoot.mk _ _)
    simp
    exact congr($(hAlg) x)
  show f (AdjoinRoot.mk _ _) = g (AdjoinRoot.mk _ _)
  simpa

-- TODO: replace `liftHom` by this
def liftAlgHom (i : S →ₐ[R] T) (x : T) (h : p.eval₂ i x = 0) : AdjoinRoot p →ₐ[R] T where
  __ := lift i.toRingHom _ h
  commutes' r := by
    simp [lift_of h, AdjoinRoot.algebraMap_eq']

@[simp]
lemma coe_liftAlgHom (i : S →ₐ[R] T) (x : T) (h : p.eval₂ i x = 0) :
    (liftAlgHom i x h : AdjoinRoot p →+* T) = lift i.toRingHom _ h :=
  rfl

@[simp]
lemma liftAlgHom_of {s : S} {i : S →ₐ[R] T} {x : T} {h : p.eval₂ i x = 0} :
    liftAlgHom i x h (of p s) = i s := by simp [liftAlgHom]

@[simp]
lemma liftAlgHom_root {i : S →ₐ[R] T} {x : T} {h : p.eval₂ i x = 0} :
    liftAlgHom i x h (root p) = x := by simp [liftAlgHom]

variable (p q) in
-- TODO : find better name
def map (f : S →+* T) (h: p.map f = q) : AdjoinRoot p →+* AdjoinRoot q :=
  lift ((algebraMap T _).comp f) (root q) (by
    rw [← Polynomial.eval₂_map, ← Polynomial.aeval_def, aeval_eq, h, mk_self])

@[simp]
lemma map_of {s : S} {f : S →+* T} {h: p.map f = q} : map p q f h ((of p) s) = f s := by
  simp [map]

@[simp]
lemma map_root {f : S →+* T} {h: p.map f = q} : map p q f h (root p) = root q := by simp [map]

variable (p q) in
def mapAlgHom (f : S →ₐ[R] T) (h : p.map f = q) : AdjoinRoot p →ₐ[R] AdjoinRoot q where
  __ := map p q f h
  commutes' r := by
    simp [map, AdjoinRoot.algebraMap_eq']

variable (p q) in
@[simp]
lemma coe_mapAlgHom (f : S →ₐ[R] T) (h : p.map f = q) : ⇑(mapAlgHom p q f h) = map p q f h := rfl

lemma mapAlgHom_mapAlghom {f : S →ₐ[R] T} {g : T →ₐ[R] U} {h₁ : p.map f = q} {h₂ : q.map g = u} :
    (mapAlgHom q u g h₂).comp (mapAlgHom p q f h₁) =
    mapAlgHom p u (g.comp f) (by simp [AlgHom.comp_toRingHom, ← Polynomial.map_map, h₁, h₂]) := by
  aesop

variable (p q) in
def mapAlgEquiv (f : S ≃ₐ[R] T) (h : p.map f = q) : AdjoinRoot p ≃ₐ[R] AdjoinRoot q :=
  .ofAlgHom
    (mapAlgHom p q f h)
    (mapAlgHom q p f.symm (by simp [← h, Polynomial.map_map, ← AlgEquiv.toRingHom_trans]))
    (by ext <;> simp)
    (by ext <;> simp)

variable (p q) in
@[simp]
lemma coe_mapAlgEquiv (f : S ≃ₐ[R] T) (h : p.map f = q) : ⇑(mapAlgEquiv p q f h) = map p q f h :=
  rfl

end

open Algebra TensorProduct

-- TODO: get rid of rfl
variable (p) in
def tensorAlgEquiv (q : Polynomial (T ⊗[R] S))
    (h : p.map includeRight.toRingHom = q) :
    T ⊗[R] AdjoinRoot p ≃ₐ[T] AdjoinRoot q := by
  refine .ofAlgHom (Algebra.TensorProduct.lift (algHom T T _) (mapAlgHom _ _ includeRight h) ?_)
      (liftAlgHom (Algebra.TensorProduct.map (AlgHom.id T T)
      (((Algebra.ofId S (AdjoinRoot p))).restrictScalars R)) (1 ⊗ₜ (root _)) ?_) ?_ ?_
  · exact fun _ _ ↦ .all ..
  · simp [← h]
    rw [Polynomial.eval₂_map]
    change Polynomial.eval₂ ((Algebra.TensorProduct.map (AlgHom.id R T) _).comp _).toRingHom _ _ = _
    simp only [map_comp_includeRight, AlgHom.toRingHom_eq_coe, AlgHom.comp_toRingHom,
      AlgHom.coe_restrictScalars, ← Polynomial.eval₂_map]
    change Polynomial.eval₂ _ ((RingHomClass.toRingHom includeRight) (root p)) (p.map (of _)) = _
    rw [Polynomial.eval₂_hom]
    simp [Polynomial.eval_map]
  · ext
    · simp [Algebra.ofId_apply, AdjoinRoot.algebraMap_eq', ← AlgHom.toRingHom_eq_coe]
      rfl
    simp
  · ext : 1
    · ext
    ext : 2 <;> simp [Algebra.ofId_apply, AdjoinRoot.algebraMap_eq', ← AlgHom.toRingHom_eq_coe]
    rfl

variable (p) in
@[simp]
lemma tensorAlgEquiv_root {q : Polynomial (T ⊗[R] S)}
    {h : p.map includeRight.toRingHom = q} :
    tensorAlgEquiv p q h (1 ⊗ₜ root p) = root q := by simp [tensorAlgEquiv]

variable (p) in
@[simp]
lemma tensorAlgEquiv_of (q : Polynomial (T ⊗[R] S)) (h : p.map includeRight.toRingHom = q) {x : S} :
    tensorAlgEquiv p q h (1 ⊗ₜ of p x) = of q (1 ⊗ₜ x):= by simp [tensorAlgEquiv]

end AdjoinRoot
