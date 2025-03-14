import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] [IsDomain R]
  [IsPrincipalIdealRing R] [Module.Finite R M] [NoZeroSMulDivisors R M] [Module.Free R M]

variable (R M) in
noncomputable def linearEquivPiFree : M ≃ₗ[R] (Fin (Module.finrank R M) → R) :=
  (Module.Free.repr R M).trans <| .trans
    (Finsupp.domLCongr <| .trans (.refl _) <| Finite.equivFinOfCardEq
      (Module.finrank_eq_nat_card_basis <| Module.Free.chooseBasis R M).symm)
    (Pi.basisFun _ _).repr.symm
