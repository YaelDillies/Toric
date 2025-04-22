import Mathlib.RingTheory.Bialgebra.Hom

open Coalgebra TensorProduct

namespace BialgHom
variable {R A B : Type*} [CommSemiring R] [Semiring A] [Bialgebra R A] [Semiring B] [Bialgebra R B]

/-- Construct a bialgebra hom from an algebra hom respecting counit and comultiplication. -/
@[simps] def ofAlgHom (f : A →ₐ[R] B) (counit_comp : counit ∘ₗ f.toLinearMap = counit)
    (map_comp_comul : map f.toLinearMap f.toLinearMap ∘ₗ comul = comul ∘ₗ f.toLinearMap) :
    A →ₐc[R] B where
  __ := f
  map_smul' := map_smul f
  counit_comp := counit_comp
  map_comp_comul := map_comp_comul

attribute [simp] coe_toCoalgHom

lemma toCoalgHom_apply (f : A →ₐc[R] B) (a : A) : f.toCoalgHom a = f a := rfl

end BialgHom

namespace Bialgebra
variable {R A : Type*} [CommSemiring R]

section Semiring
variable [Semiring A] [Bialgebra R A]

variable (R A) in
def unitCoalgHom : R →ₗc[R] A where
  __ := Algebra.ofId R A
  map_smul' a b := by simp [map_mul, Algebra.smul_def, Algebra.ofId]
  counit_comp := by ext; simp
  map_comp_comul := by ext; simp [Algebra.TensorProduct.one_def]

variable (R A) in
def unitBialgHom : R →ₐc[R] A where
  __ := Algebra.ofId R A
  __ := unitCoalgHom R A

end Semiring

section CommSemiring

section Algebra
variable [CommSemiring A] [Algebra R A]

-- TODO: Move this somewhere more appropriate
variable (R A) in
noncomputable def mulAlgHom : A ⊗[R] A →ₐ[R] A :=
  .ofLinearMap (.mul' R A) (by simp [Algebra.TensorProduct.one_def]) fun x y ↦ by
    induction x <;> induction y <;> simp [mul_mul_mul_comm, mul_add, add_mul, *]; sorry

end Algebra

section Bialgebra
variable [CommSemiring A] [Bialgebra R A]


variable (R A) in
noncomputable def mulCoalgHom : A ⊗[R] A →ₗc[R] A where
  __ := LinearMap.mul' R A
  map_smul' a b := by induction b <;> simp
  counit_comp := by ext; simp
  map_comp_comul := by
    ext a b
    simp
    sorry

variable (R A) in
noncomputable def mulBialgHom : A ⊗[R] A →ₐc[R] A where
  __ := mulAlgHom R A
  __ := mulCoalgHom R A

-- This is false without cocommutativity of A :)
variable (R A) in
noncomputable def comulCoalgHom : A →ₗc[R] A ⊗[R] A where
  __ := comulAlgHom R A
  map_smul' a b := by simp
  counit_comp := by ext; simp; sorry
  map_comp_comul := by
    ext a
    simp
    sorry

variable (R A) in
noncomputable def comulBialgHom : A →ₐc[R] A ⊗[R] A where
  __ := comulAlgHom R A
  __ := comulCoalgHom R A

end Bialgebra

end CommSemiring
end Bialgebra
