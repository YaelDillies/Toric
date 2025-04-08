import Mathlib.CategoryTheory.Comma.Over.Basic

namespace CategoryTheory.Over
variable {C : Type*} [Category C] {X : C}

open Limits

/-- If `X : C` is initial, then the under category of `X` is equivalent to `C`. -/
@[simps]
def equivalenceOfIsTerminal (hX : IsTerminal X) : Over X ≌ C where
  functor := forget X
  inverse := { obj Y := mk (hX.from Y), map f := homMk f }
  unitIso := NatIso.ofComponents (fun Y ↦ isoMk (.refl _) (hX.hom_ext _ _))
  counitIso := NatIso.ofComponents (fun _ ↦ .refl _)

instance : (Over.opToOpUnder X).EssSurj := (Over.opEquivOpUnder X).essSurj_functor
instance : (Under.opToOverOp X).EssSurj := (Over.opEquivOpUnder X).essSurj_inverse
instance : (Under.opToOpOver X).EssSurj := (Under.opEquivOpOver X).essSurj_functor
instance : (Over.opToUnderOp X).EssSurj := (Under.opEquivOpOver X).essSurj_inverse

end CategoryTheory.Over

namespace CategoryTheory.Functor
variable {C D : Type*} [Category C] [Category D] {X : C} {F : C ⥤ D}

/-- The essential of the slice of a full functor is the same as the essential image of the original
functor. -/
@[simp] lemma essImage_overPost [F.Full] {Y : Over (F.obj X)} :
    (Over.post F (X := X)).essImage Y ↔ F.essImage Y.left where
  mp := fun ⟨Z, ⟨e⟩⟩ ↦ ⟨Z.left, ⟨(Over.forget _).mapIso e⟩⟩
  mpr := fun ⟨Z, ⟨e⟩⟩ ↦ let ⟨f, hf⟩ := F.map_surjective (e.hom ≫ Y.hom); ⟨.mk f, ⟨Over.isoMk e⟩⟩

/-- The essential of the slice of a full functor is the same as the essential image of the original
functor. -/
@[simp] lemma essImage_underPost [F.Full] {Y : Under (F.obj X)} :
    (Under.post F (X := X)).essImage Y ↔ F.essImage Y.right where
  mp := fun ⟨Z, ⟨e⟩⟩ ↦ ⟨Z.right, ⟨(Under.forget _).mapIso e⟩⟩
  mpr := fun ⟨Z, ⟨e⟩⟩ ↦ let ⟨f, hf⟩ := F.map_surjective (Y.hom ≫ e.inv); ⟨.mk f, ⟨Under.isoMk e⟩⟩

end CategoryTheory.Functor
