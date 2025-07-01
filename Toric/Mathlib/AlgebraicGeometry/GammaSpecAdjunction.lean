import Mathlib.AlgebraicGeometry.GammaSpecAdjunction

namespace AlgebraicGeometry
variable {R S : CommRingCat}

instance : Scheme.Γ.rightOp.IsLeftAdjoint := ΓSpec.adjunction.isLeftAdjoint

@[simp] lemma Spec.map_preimage_unop (f : Spec R ⟶ Spec S) :
    Spec.map (Spec.fullyFaithful.preimage f).unop = f := Spec.fullyFaithful.map_preimage _

end AlgebraicGeometry
