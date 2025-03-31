import Mathlib.CategoryTheory.Comma.Over.Basic

namespace CategoryTheory.Functor
variable {C D : Type*} [Category C] [Category D] {F : C ⥤ D} (X : C)

/-- If `F` is fully faithful, also `Over.post F` is fully faithful. -/
def FullyFaithful.over (h : F.FullyFaithful) : (Over.post (X := X) F).FullyFaithful where
  preimage {A B} f := Over.homMk (h.preimage f.left) <|
    h.map_injective (by simpa using Over.w f)

end CategoryTheory.Functor
