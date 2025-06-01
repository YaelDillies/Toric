import Mathlib.CategoryTheory.Functor.FullyFaithful

namespace CategoryTheory

/-- Given a natural isomorphism between `F ⋙ H` and `G ⋙ H` for a fully faithful functor `H`, we
can 'cancel' it to give a natural iso between `F` and `G`. -/
noncomputable def Functor.FullyFaithful.cancelRight {C : Type*} [Category C]
  {D : Type*} [Category D] {E : Type*} [Category E] {F G : C ⥤ D} {H : D ⥤ E}
    (HH : H.FullyFaithful) (comp_iso : F ⋙ H ≅ G ⋙ H) : F ≅ G :=
  NatIso.ofComponents (fun X => HH.preimageIso (comp_iso.app X)) fun f =>
    HH.map_injective (by simpa using comp_iso.hom.naturality f)

end CategoryTheory
