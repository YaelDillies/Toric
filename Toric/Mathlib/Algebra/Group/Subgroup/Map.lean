import Mathlib.Algebra.Group.Subgroup.Map

namespace MulEquiv
variable {G H: Type*} [Group G] [Group H]

open Subgroup

attribute [to_additive] comapSubgroup

@[to_additive (attr := simp, norm_cast)]
lemma coe_comapSubgroup (e : G ≃* H) : comapSubgroup e = comap e.toMonoidHom := rfl

@[to_additive (attr := simp)]
lemma symm_comapSubgroup (e : G ≃* H) : (comapSubgroup e).symm = comapSubgroup e.symm := rfl

--TODO: do the same thing for mapSubgroup

end MulEquiv

namespace Subgroup
variable {G H: Type*} [Group G] [Group H]

@[to_additive (attr := simp, norm_cast)]
lemma comap_toSubmonoid (e : G ≃* H) (s : Subgroup H) :
    (s.comap e).toSubmonoid = s.toSubmonoid.comap e.toMonoidHom := rfl

end Subgroup
