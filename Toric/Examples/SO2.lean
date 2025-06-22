/-
Copyright (c) 2025 Yaël Dillies, Michał Mrugała, Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Michał Mrugała, Andrew Yang
-/
import Mathlib.Data.Complex.FiniteDimensional
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.RingTheory.AdjoinRoot
import Toric.Mathlib.RingTheory.HopfAlgebra.GroupLike
import Toric.GroupScheme.Torus
import Toric.Mathlib.Algebra.Polynomial.AlgebraMap
import Toric.Mathlib.AlgebraicGeometry.Over
import Toric.Mathlib.Data.Finsupp.Single
import Toric.Mathlib.LinearAlgebra.UnitaryGroup
import Toric.Mathlib.RingTheory.AdjoinRoot
import Toric.Mathlib.RingTheory.HopfAlgebra.GroupLike

namespace MonoidHom
variable {G M : Type*} [Group G] [CommMonoid M]

@[simp] lemma toHomUnits_mul (f g : G →* M) : (f * g).toHomUnits = f.toHomUnits * g.toHomUnits := by
  ext; rfl

/-- `MonoidHom.toHomUnits` as a `MulEquiv`. -/
def toHomUnitsMulEquiv : (G →* M) ≃* (G →* Mˣ) where
  toFun := toHomUnits
  invFun f := (Units.coeHom _).comp f
  map_mul' := by simp

end MonoidHom

noncomputable section

local notation3:max R "[X][Y]" => Polynomial (Polynomial R)
local notation3:max "Y" => Polynomial.C (Polynomial.X)

open Coalgebra Polynomial TensorProduct
open scoped Mon_Class

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]


variable (R) in
abbrev SO2Ring : Type _ := AdjoinRoot (X ^ 2 + Y ^ 2 - 1 : R[X][Y])

namespace SO2Ring

instance : CommRing (SO2Ring R) := by delta SO2Ring; infer_instance
instance : Algebra R (SO2Ring S) := by delta SO2Ring; infer_instance
instance : IsScalarTower R S (SO2Ring S) := by delta SO2Ring; infer_instance

def mk : R[X][Y] →ₐ[R] SO2Ring R := Ideal.Quotient.mkₐ R _

nonrec def X : SO2Ring R := .mk X
nonrec def «Y» : SO2Ring R := .mk Y

@[simp] lemma X_def : mk .X = .X (R := R) := rfl
@[simp] lemma Y_def : mk Y = .Y (R := R) := rfl

--TODO : make equiv
def liftₐ (x y : S) (H : x ^ 2 + y ^ 2 = 1) : SO2Ring R →ₐ[R] S :=
  Ideal.Quotient.liftₐ _ (aevalAEval x y)
    (show Ideal.span _ ≤ RingHom.ker _ by simp [Ideal.span_le, Set.singleton_subset_iff, H])

@[simp]
lemma liftₐ_X (x y : S) (H : x ^ 2 + y ^ 2 = 1) : liftₐ (R := R) x y H .X = x := aevalAEval_X ..

@[simp]
lemma liftₐ_Y (x y : S) (H : x ^ 2 + y ^ 2 = 1) : liftₐ (R := R) x y H .Y = y := aevalAEval_Y ..

@[simp]
lemma relation : SO2Ring.X (R := R) ^ 2 + .Y ^ 2 = 1 := by
  simp_rw [SO2Ring.X, SO2Ring.Y, ← map_pow, ← map_add, ← map_one SO2Ring.mk]
  exact Ideal.Quotient.eq.mpr <| by simp [Ideal.mem_span_singleton]

lemma relation' : SO2Ring.X (R := R) ^ 2 = 1 - .Y ^ 2 := by simp [← relation]

@[simp] lemma relation'' : SO2Ring.X (R := R) * .X + .Y * .Y = 1 := by simp [← pow_two]

@[ext]
lemma algebraMap_ext {A : Type*} [Semiring A] [Algebra R A] {f g : SO2Ring R →ₐ[R] A}
    (h1 : f .X = g .X) (h2 : f .Y = g .Y) : f = g := by
  simp_rw [SO2Ring] at f g; apply Ideal.Quotient.algHom_ext; ext <;> assumption

def comulAlgHom : SO2Ring R →ₐ[R] SO2Ring R ⊗[R] SO2Ring R := by
  refine liftₐ (.X ⊗ₜ .X - .Y ⊗ₜ .Y) (.X ⊗ₜ .Y + .Y ⊗ₜ .X) ?_
  ring_nf
  simp only [Algebra.TensorProduct.tmul_mul_tmul,
    Algebra.TensorProduct.tmul_pow (A := SO2Ring R) (B := SO2Ring R), relation', tmul_sub,
    sub_tmul, ← Algebra.TensorProduct.one_def (A := SO2Ring R) (B := SO2Ring R)]
  ring_nf

@[simp]
lemma comulAlgHom_apply_X : comulAlgHom (R := R) .X = (.X ⊗ₜ .X - .Y ⊗ₜ .Y) := by
  simp [comulAlgHom]

@[simp]
lemma comulAlgHom_apply_Y : comulAlgHom (R := R) .Y = (.X ⊗ₜ .Y + .Y ⊗ₜ .X) := by
  simp [comulAlgHom]

def counitAlgHom : SO2Ring R →ₐ[R] R := liftₐ 1 0 (by simp)

@[simp] lemma counitAlgHom.apply_X : counitAlgHom (R := R) .X = 1 := by simp [counitAlgHom]
@[simp] lemma counitAlgHom.apply_Y : counitAlgHom (R := R) .Y = 0 := by simp [counitAlgHom]

instance : Bialgebra R (SO2Ring R) := .ofAlgHom comulAlgHom counitAlgHom
  (by ext <;> simp [sub_tmul, tmul_sub, tmul_add, add_tmul] <;> ring)
  (by ext <;> simp [sub_tmul, tmul_sub, tmul_add, add_tmul])
  (by ext <;> simp [sub_tmul, tmul_sub, tmul_add, add_tmul])

@[simp] lemma comul_def : comul (R := R) (A := SO2Ring R) = comulAlgHom (R := R) := rfl
@[simp] lemma counit_def : counit (R := R) (A := SO2Ring R) = counitAlgHom (R := R) := rfl

def antipodeAlgHom : SO2Ring R →ₐ[R] SO2Ring R := liftₐ .X (-.Y) (by simp)

@[simp] lemma antipodeAlgHom_X : antipodeAlgHom (R := R) .X = X := by simp [antipodeAlgHom]
@[simp] lemma antipodeAlgHom_Y : antipodeAlgHom (R := R) .Y = -.Y := by simp [antipodeAlgHom]

instance : HopfAlgebra R (SO2Ring R) := by
  refine .ofAlgHom antipodeAlgHom ?_ <| by ext <;> simp; ring_nf
  ext
  · simp [← sq]
  · simp
    ring_nf

@[simp] lemma antipode_X : antipode R X = X (R := R) := antipodeAlgHom_X
@[simp] lemma antipode_Y : antipode R SO2Ring.Y = - .Y (R := R) := antipodeAlgHom_Y

private lemma foo : (SO2Ring.X (R := ℂ)) ^ 2 - (Complex.I • SO2Ring.Y) ^ 2 = 1 := calc
  _ = .X ^ 2 - (Complex.I • .Y) * (Complex.I • .Y) := by ring
  _ = .X ^ 2 - (Complex.I) ^ 2 • .Y ^ 2 := by
    rw [Algebra.mul_smul_comm, Algebra.smul_mul_assoc, smul_smul]
    ring_nf
  _ = _ := by simp

@[simps!]
def T : GroupLike ℂ (SO2Ring ℂ) where
  val := .X + Complex.I • .Y
  isGroupLikeElem_val := ⟨by simp, by
    simp [sub_tmul, tmul_sub, tmul_add, add_tmul, ← smul_tmul', smul_smul]
    ring_nf⟩

private def complexEquivFun : MonoidAlgebra ℂ (Multiplicative ℤ) →ₐc[ℂ] SO2Ring ℂ := by
  refine (MonoidAlgebra.liftGroupLikeBialgHom _ _).comp <|
    MonoidAlgebra.mapDomainBialgHom ℂ (M := Multiplicative ℤ) <| AddMonoidHom.toMultiplicative''  <|
     zmultiplesHom _ <| .ofMul T

private lemma complexEquivFun_single (a : Multiplicative ℤ) (b : ℂ) :
    complexEquivFun (.single a b) = b • (T ^ a.toAdd).1 := by
  simp [complexEquivFun, Algebra.ofId_apply, Algebra.smul_def]

set_option allowUnsafeReducibility true in
attribute [local semireducible] MonoidAlgebra.single in
private def complexEquivInv : SO2Ring ℂ →ₐc[ℂ] MonoidAlgebra ℂ (Multiplicative ℤ) := by
  refine .ofAlgHom'
    (liftₐ
      ((1 / 2 : ℂ) • (.single (.ofAdd 1) 1 + .single (.ofAdd (-1)) 1))
      (- (.I / 2 : ℂ) • (.single (.ofAdd 1) 1 - .single (.ofAdd (-1)) 1)) ?_) ?_ ?_
  · simp [pow_two, sub_mul, mul_sub, add_mul, mul_add, MonoidAlgebra.single_mul_single, ← ofAdd_add,
      ← two_nsmul, ← mul_smul, ← mul_inv_rev, div_mul_div_comm, neg_div, smul_sub,
      MonoidAlgebra.one_def]
    module
  · ext <;> simp [MonoidAlgebra.counit_single]; norm_num
  · ext
    · simp [MonoidAlgebra.comul_single, smul_add, tmul_add, add_tmul, smul_sub, sub_tmul,
        tmul_sub, neg_tmul, tmul_neg, ← smul_tmul', tmul_smul, smul_smul, div_mul_div_comm,
        Complex.I_mul_I]
      module
    · simp [MonoidAlgebra.comul_single, smul_add, tmul_add, add_tmul, smul_sub, sub_tmul, tmul_sub,
        neg_tmul, tmul_neg, ← smul_tmul', tmul_smul, smul_smul, div_mul_div_comm, Complex.I_mul_I]
      module

def complexEquiv : MonoidAlgebra ℂ (Multiplicative ℤ) ≃ₐc[ℂ] SO2Ring ℂ where
  __ := complexEquivFun
  __ : MonoidAlgebra ℂ (Multiplicative ℤ) ≃ₐ[ℂ] SO2Ring ℂ := by
    refine .ofAlgHom (AlgHomClass.toAlgHom complexEquivFun) complexEquivInv ?_ ?_
    · ext
      · simp [complexEquivFun_single, complexEquivInv]
        module
      simp [complexEquivInv, complexEquivFun_single, ←two_smul, smul_smul, div_mul_eq_mul_div,
         -nsmul_eq_mul]
      module
    · ext
      simp [complexEquivFun_single, complexEquivInv, smul_smul, mul_div, smul_sub, neg_div,
        MonoidAlgebra.single, ← sub_eq_add_neg, ← Finsupp.single_add_apply, -Finsupp.single_add]
      norm_num

@[simp] lemma complexEquiv_single (a : Multiplicative ℤ) (b : ℂ) :
    complexEquiv (.single a b) = b • (T ^ a.toAdd).1 := complexEquivFun_single ..

@[simp] lemma complexEquiv_comp_algebraMap :
    .comp complexEquiv (algebraMap ℂ <| MonoidAlgebra ℂ <| Multiplicative ℤ) =
      algebraMap ℂ (SO2Ring ℂ) := by ext; simp [Algebra.algebraMap_eq_smul_one]

open Matrix

def algHomMulEquiv : (SO2Ring R →ₐ[R] S) ≃* specialOrthogonalGroup (Fin 2) S where
  toFun f := ⟨!![f .X, f .Y; - f .Y, f .X], by
    simp [← map_mul, ← map_add, mem_specialOrthogonalGroup_fin_two_iff, pow_two]⟩
  invFun M := SO2Ring.liftₐ (M.1 0 0) (M.1 0 1)
    (mem_specialOrthogonalGroup_fin_two_iff.mp M.2).2.2
  left_inv f := by ext <;> simp
  right_inv M := by ext i j; fin_cases i, j <;>
    simp [(mem_specialOrthogonalGroup_fin_two_iff.mp M.2).2.1,
      (mem_specialOrthogonalGroup_fin_two_iff.mp M.2).1]
  map_mul' f g := by
    ext i j
    fin_cases i, j
    · simp [sub_eq_add_neg]
    · simp [sub_eq_add_neg]
    · simp [sub_eq_add_neg]
    · simp [sub_eq_neg_add]

instance : Algebra S (S ⊗[R] SO2Ring R) :=
  Algebra.TensorProduct.leftAlgebra (A := S) (B := SO2Ring R)

variable (R S) in
def baseChangeAlgEquiv : S ⊗[R] SO2Ring R ≃ₐ[S] SO2Ring S := .trans
  (AdjoinRoot.tensorAlgEquiv _ _ rfl) <|
  AdjoinRoot.mapAlgEquiv _ _ (polyEquivTensor' _ _).symm (by simp)

@[simp]
lemma baseChangeAlgEquiv_X : (baseChangeAlgEquiv R S) (1 ⊗ₜ X) = X := by
  change (baseChangeAlgEquiv R S) (1 ⊗ₜ (AdjoinRoot.root _)) = AdjoinRoot.root _
  simp [baseChangeAlgEquiv]

@[simp]
lemma baseChangeAlgEquiv_Y : (baseChangeAlgEquiv R S) (1 ⊗ₜ «Y») = «Y» := by
  change (baseChangeAlgEquiv R S) (1 ⊗ₜ (AdjoinRoot.of _ _)) = AdjoinRoot.of _ _
  simp [baseChangeAlgEquiv]

variable (R S) in
def baseChangeBialgEquiv : S ⊗[R] SO2Ring R ≃ₐc[S] SO2Ring S :=
  .ofAlgEquiv' (baseChangeAlgEquiv R S)
  (by aesop)
  (by aesop (add simp [tmul_add, tmul_sub]))

@[simp]
lemma coe_baseChangeBialgEquiv : ⇑(baseChangeBialgEquiv R S) = baseChangeAlgEquiv R S := rfl

@[simp] lemma baseChangeBialgEquiv_comp_algebraMap :
  .comp (baseChangeBialgEquiv R S) (Algebra.ofId S (S ⊗[R] SO2Ring R)) =
    Algebra.ofId S (SO2Ring S) := by ext

end SO2Ring

open AlgebraicGeometry CategoryTheory Limits SO2Ring
open scoped Hom

namespace AlgebraicGeometry.SO₂

open Scheme

scoped notation3 "SO₂("R")" => Spec <| .of <| SO2Ring R

def so₂ComplexIso : SO₂(ℂ) ≅ Diag Spec(ℂ) ℤ :=
  Scheme.Spec.mapIso complexEquiv.toAlgEquiv.toRingEquiv.toCommRingCatIso.op ≪≫
    (diagSpecIso (.of ℂ) ℤ).symm

@[simp] lemma so₂ComplexIso_hom :
    so₂ComplexIso.hom =
      ((bialgSpec <| .of ℂ).map <| .op <| CommBialgCat.ofHom complexEquiv.toBialgHom).hom.left ≫
        (diagSpecIso (.of ℂ) ℤ).inv := rfl

@[simp] lemma so₂ComplexIso_inv :
    so₂ComplexIso.inv =
      (diagSpecIso (.of ℂ) ℤ).hom ≫
        ((bialgSpec <| .of ℂ).map <| .op <|
          CommBialgCat.ofHom complexEquiv.symm.toBialgHom).hom.left := rfl

instance : so₂ComplexIso.hom.IsOver Spec(ℂ) := by rw [so₂ComplexIso_hom]; infer_instance

lemma so₂ComplexIso_hom_asOver :
    so₂ComplexIso.hom.asOver Spec(ℂ) =
      ((bialgSpec <| .of ℂ).map <| .op <| CommBialgCat.ofHom complexEquiv.toBialgHom).hom ≫
        (diagSpecIso (.of ℂ) ℤ).inv.asOver Spec(ℂ) := rfl

instance : IsMon_Hom <| so₂ComplexIso.hom.asOver Spec(ℂ) := by
  rw [so₂ComplexIso_hom_asOver]; infer_instance

instance : SO₂(ℂ).IsSplitTorusOver Spec(ℂ) := .of_iso so₂ComplexIso

def pullbackSO₂RealComplex : pullback (SO₂(ℝ) ↘ Spec(ℝ)) (Spec(ℂ) ↘ Spec(ℝ)) ≅ SO₂(ℂ) :=
  pullbackSymmetry .. ≪≫ pullbackSpecIso .. ≪≫ Scheme.Spec.mapIso
    (baseChangeBialgEquiv ℝ ℂ).symm.toAlgEquiv.toRingEquiv.toCommRingCatIso.op

@[simp] lemma pullbackSO₂RealComplex_hom :
    pullbackSO₂RealComplex.hom = (pullbackSymmetry .. ≪≫ pullbackSpecIso' ℝ ℂ (SO2Ring ℝ)).hom ≫
      ((bialgSpec <| .of ℂ).map <| .op <|
        CommBialgCat.ofHom (baseChangeBialgEquiv ℝ ℂ).symm.toBialgHom).hom.left := rfl

universe u in
instance {R S T : Type u} [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Bialgebra R T] :
    (pullbackSymmetry .. ≪≫ pullbackSpecIso' R S T).hom.IsOver Spec(S) where
  comp_over := by
    rw [← cancel_epi (pullbackSymmetry .. ≪≫ pullbackSpecIso' ..).inv,
      canonicallyOverPullback_over]
    simp [specOverSpec_over, ← Spec.map_comp, ← CommRingCat.ofHom_comp, pullbackSpecIso']
    rfl

universe u

@[reassoc (attr := simp)]
lemma pullbackSpecIso_hom_base (R S T : Type u) [CommRing R] [CommRing S] [CommRing T] [Algebra R S]
    [Algebra R T] :
    (pullbackSpecIso R S T).hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R _)) =
      pullback.fst _ _ ≫ Spec.map (CommRingCat.ofHom (algebraMap _ _)) := by
  simp [← Iso.eq_inv_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    ← Algebra.TensorProduct.algebraMap_def, ← IsScalarTower.algebraMap_eq]

@[reassoc (attr := simp)]
lemma pullbackSpecIso_hom_fst' (R S T : Type u) [CommRing R] [CommRing S] [CommRing T] [Algebra R S]
    [Algebra R T] :
    (pullbackSpecIso R S T).hom ≫ Spec.map (CommRingCat.ofHom (algebraMap S _)) =
      pullback.fst _ _ := by
  simp [← Iso.eq_inv_comp, pullbackSpecIso_inv_fst, ← Algebra.TensorProduct.algebraMap_def]

@[reassoc (attr := simp)]
lemma pullbackSpecIso_inv_fst' (R S T : Type u) [CommRing R] [CommRing S] [CommRing T] [Algebra R S]
    [Algebra R T] :
    (pullbackSpecIso R S T).inv ≫ pullback.fst _ _ =
    Spec.map (CommRingCat.ofHom (algebraMap S _)) := by
  simp [← cancel_epi (pullbackSpecIso R S T).hom]

@[reassoc (attr := simp)]
lemma pullbackSpecIso_hom_snd' (R S T : Type u) [CommRing R] [CommRing S] [CommRing T] [Algebra R S]
    [Algebra R T] :
    (pullbackSpecIso R S T).hom ≫ Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight (R := R) (A := S) (B := T) : _ →+* _)) =
      pullback.snd _ _ := by
  simp [← Iso.eq_inv_comp, pullbackSpecIso_inv_fst, ← Algebra.TensorProduct.algebraMap_def]

lemma pullbackSpecIso'_symmetry {R S T: Type u} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Bialgebra R T] : (pullbackSymmetry .. ≪≫ pullbackSpecIso' R S T).hom =
    (pullbackSpecIso' ..).hom ≫
    Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.comm R S T)) := by
  simp_rw [Iso.trans_hom, ← Iso.eq_comp_inv, Category.assoc, ← Iso.inv_comp_eq]
  ext
  · have : (RingHomClass.toRingHom (Algebra.TensorProduct.comm R S T)).comp
      Algebra.TensorProduct.includeLeftRingHom = Algebra.TensorProduct.includeRight.toRingHom := rfl
    simp [specOverSpec_over, pullbackSpecIso', ← Spec.map_comp, ← CommRingCat.ofHom_comp, this]
  have : (RingHomClass.toRingHom (Algebra.TensorProduct.comm R S T)).comp
      (RingHomClass.toRingHom Algebra.TensorProduct.includeRight) =
      Algebra.TensorProduct.includeLeftRingHom := rfl
  simp [specOverSpec_over, pullbackSpecIso', ← Spec.map_comp, ← CommRingCat.ofHom_comp, this]

lemma foo (R S T : Type u) [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Bialgebra R T] :
      (Functor.LaxMonoidal.μ (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R S))))
        (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R T))))
        (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R T))))).left ≫
    pullback.fst _ _ ≫
      (pullbackSpecIso R T T).hom =
    (MonoidalCategoryStruct.tensorHom
        ((pullbackSymmetry .. ≪≫ pullbackSpecIso' R S T).hom.asOver (Spec(S)))
        ((pullbackSymmetry .. ≪≫ pullbackSpecIso' R S T).hom.asOver (Spec(S)))).left ≫
    (pullbackSpecIso S (S ⊗[R] T) (S ⊗[R] T)).hom ≫
    Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.mapRingHom (algebraMap _ _)
      Algebra.TensorProduct.includeRight.toRingHom
      Algebra.TensorProduct.includeRight.toRingHom
      (by simp [← IsScalarTower.algebraMap_eq])
      (by simp [← IsScalarTower.algebraMap_eq]))) := by
  rw [← cancel_mono (pullbackSpecIso ..).inv]
  simp
  ext <;> simp
  · simp only [← Spec.map_comp, ← CommRingCat.ofHom_comp,
      Algebra.TensorProduct.mapRingHom_comp_includeLeftRingHom]
    simp [specOverSpec_over]
    erw [Over.tensorHom_left_fst_assoc]
    simp [pullbackSpecIso']
    rfl
  · simp only [← Spec.map_comp, ← CommRingCat.ofHom_comp,
      Algebra.TensorProduct.mapRingHom_comp_includeRight]
    simp [specOverSpec_over]
    erw [Over.tensorHom_left_snd_assoc]
    simp [pullbackSpecIso']
    rfl

theorem name1
  {R S T : Type u} [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Bialgebra R T] :
    (RingHomClass.toRingHom (Bialgebra.comulAlgHom S (S ⊗[R] T))).comp
    (RingHomClass.toRingHom (Algebra.TensorProduct.includeRight (R := R) (A := S) (B := T))) =
    (Algebra.TensorProduct.mapRingHom (algebraMap R S)
    (RingHomClass.toRingHom (Algebra.TensorProduct.includeRight (R := R) (A := S) (B := T)))
    (RingHomClass.toRingHom (Algebra.TensorProduct.includeRight (R := R) (A := S) (B := T)))
    (by simp; rfl)
    (by simp; rfl)).comp
    (RingHomClass.toRingHom (Bialgebra.comulAlgHom R T)) := by
  ext x
  simp [← (ℛ R x).eq, tmul_sum]

instance {R S T : Type u} [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Bialgebra R T] :
    IsMon_Hom <| (pullbackSymmetry .. ≪≫ pullbackSpecIso' R S T).hom.asOver Spec(S) where
  one_hom := by
    ext
    rw [← cancel_mono (pullbackSpecIso' ..).inv]
    ext
    · simp [mon_ClassAsOverPullback_one, algSpec_ε_left (R := CommRingCat.of _),
      pullbackSpecIso', specOverSpec_over, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← Algebra.TensorProduct.algebraMap_def]
    · simp [mon_ClassAsOverPullback_one, algSpec_ε_left (R := CommRingCat.of _),
        pullbackSpecIso', specOverSpec_over, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
        ← Algebra.TensorProduct.algebraMap_def,
        ← AlgHom.coe_restrictScalars R (Bialgebra.counitAlgHom S _), - AlgHom.coe_restrictScalars,
        ← AlgHom.comp_toRingHom, Bialgebra.counitAlgHom_comp_includeRight]
      rfl
  mul_hom := by
    ext
    rw [← cancel_mono (pullbackSpecIso' ..).inv]
    ext
    · simp [mon_ClassAsOverPullback_mul, pullbackSpecIso', specOverSpec_over, ← Spec.map_comp,
        ← CommRingCat.ofHom_comp, asOver, OverClass.asOver, AlgebraicGeometry.Scheme.mul_left,
        ← Algebra.TensorProduct.algebraMap_def, Hom.asOver, OverClass.asOverHom,
        pullback.condition]
      rfl
    · convert congr($(foo R S T) ≫
        Spec.map (CommRingCat.ofHom (Bialgebra.comulAlgHom R T).toRingHom)) using 1
      · simp [mon_ClassAsOverPullback_mul, pullbackSpecIso', specOverSpec_over, OverClass.asOver,
          Hom.asOver, OverClass.asOverHom, mul_left]
      · simp [mon_ClassAsOverPullback_mul, pullbackSpecIso', specOverSpec_over, OverClass.asOver,
          Hom.asOver, OverClass.asOverHom, mul_left, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
          name1]

-- generalize this
instance : (pullbackSymmetry .. ≪≫ pullbackSpecIso' ℝ ℂ (SO2Ring ℝ)).hom.IsOver Spec(ℂ) where
  comp_over := by
    rw [← cancel_epi (pullbackSymmetry .. ≪≫ pullbackSpecIso' ..).inv, canonicallyOverPullback_over]
    simp [specOverSpec_over, pullbackSpecIso']

instance : pullbackSO₂RealComplex.hom.IsOver Spec(ℂ) := by
  rw [pullbackSO₂RealComplex_hom]; infer_instance

@[simp] lemma pullbackSO₂RealComplex_hom_asOver :
    pullbackSO₂RealComplex.hom.asOver Spec(ℂ) =
      (pullbackSymmetry .. ≪≫ pullbackSpecIso' ℝ ℂ (SO2Ring ℝ)).hom.asOver Spec(ℂ) ≫
        ((bialgSpec <| .of ℂ).map <| .op <|
          CommBialgCat.ofHom (baseChangeBialgEquiv ℝ ℂ).symm.toBialgHom).hom := rfl

instance : IsMon_Hom <| pullbackSO₂RealComplex.hom.asOver Spec(ℂ) := by
  rw [pullbackSO₂RealComplex_hom_asOver]; infer_instance

instance pullback_SO₂_real_isSplitTorusOver_complex :
    (pullback (SO₂(ℝ) ↘ Spec(ℝ)) (Spec(ℂ) ↘ Spec(ℝ))).IsSplitTorusOver Spec(ℂ) :=
  .of_iso pullbackSO₂RealComplex

/-- `SO(2)` is a split torus over the reals. -/
instance : Spec(SO2Ring ℝ).IsTorusOver ℝ where
  existsSplit :=
    ⟨ℂ, inferInstance, inferInstance, inferInstance, pullback_SO₂_real_isSplitTorusOver_complex⟩

open Matrix

variable (R) in
def bar : (Spec(R).asOver Spec(R) ⟶ SO₂(R).asOver Spec(R)) ≃* specialOrthogonalGroup (Fin 2) R :=
  Spec.mulEquiv.symm.trans algHomMulEquiv

def SplitTorus.mulEquiv (R : CommRingCat.{u}) (σ : Type u) :
    (σ → Rˣ) ≃* ((Spec R).asOver (Spec R) ⟶ (SplitTorus (Spec R) σ).asOver (Spec R)) := by
  refine (MvLaurentPolynomial.liftEquiv (R := R) ..).trans ?_
  refine Spec.mulEquiv.trans ?_
  dsimp
  haveI : IsMon_Hom (Iso.asOver (Spec R) (splitTorusIso R σ)).hom := by
    change IsMon_Hom ((splitTorusIso R σ).hom.asOver _)
    infer_instance
  exact ((yonedaGrp.mapIso (Grp_.mkIso' ((Scheme.splitTorusIso R σ).asOver (Spec R)))).app
    (.op ((Spec R).asOver (Spec R)))).groupIsoToMulEquiv.symm

def I : specialOrthogonalGroup (Fin 2) ℝ :=
  ⟨!![0, 1; -1, 0], by simp [mem_specialOrthogonalGroup_fin_two_iff]⟩

lemma I_sq_ne_1 : I ^ 2 ≠ 1 := by
  intro h
  have := congr_fun₂ congr(($h).val) 0 0
  norm_num [I, pow_two] at this

@[simp] lemma I_ord_4' : I ^ 4 = 1 := by simp [I, pow_succ, one_fin_two]

private lemma aux1 {x : ℝ} : x ^ 4 = 1 ↔ x ^ 2 = 1 := by
  simpa [← pow_mul] using sq_eq_sq₀ (sq_nonneg x) zero_le_one

private lemma aux2 {σ : Type*} {x : σ → ℝˣ} : x ^ 4 = 1 → x ^ 2 = 1 := by
  simp [aux1, funext_iff, ← Units.val_eq_one]

private lemma aux3 (σ : Type*) : IsEmpty <| specialOrthogonalGroup (Fin 2) ℝ ≃* (σ → ℝˣ) := by
  constructor
  intro e
  have h₁ : e I ^ 4 = 1 := by simp [← map_pow]
  have h₂ : e I ^ 2 ≠ 1 := by
    rw [← map_pow, ← e.map_one, e.injective.ne_iff]
    exact I_sq_ne_1
  exact h₂ <| aux2 h₁

instance : Algebra.FiniteType ℝ (SO2Ring ℝ) := sorry

open scoped AddMonoidAlgebra

/-- `SO(2)` is not a split torus over the real numbers. -/
theorem not_isSplitTorusOver_SO₂_real : ¬ SO₂(ℝ).IsSplitTorusOver Spec(ℝ) := by
  intro
  obtain ⟨σ, _, e, _, _⟩ := exists_iso_diag_finite_of_isSplitTorusOver_locallyOfFiniteType SO₂(ℝ)
    Spec(ℝ)
  haveI : (e ≪≫ diagSpecIso _ ℤ[σ]).hom.IsOver Spec(ℝ) := by dsimp; infer_instance
  haveI : IsMon_Hom ((e ≪≫ diagSpecIso _ ℤ[σ]).asOver Spec(ℝ)).hom := by dsimp; infer_instance
  have e₁ := Mon_Class.homMulEquivRight ((e ≪≫ diagSpecIso _ ℤ[σ]).asOver Spec(ℝ))
    (Spec(ℝ).asOver Spec(ℝ))
  refine (aux3 σ).1 <| (bar ℝ).symm.trans <| e₁.trans <| Spec.mulEquiv.symm.trans <|
    (MonoidAlgebra.liftMulEquiv ..).symm.trans <| MonoidHom.toHomUnitsMulEquiv.trans <|
      MonoidHom.toAdditive''MulEquiv.trans <| Finsupp.liftAddHom.symm.toMultiplicative.trans ?_
  sorry

end AlgebraicGeometry.SO₂
