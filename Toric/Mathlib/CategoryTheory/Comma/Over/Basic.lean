import Mathlib.CategoryTheory.Comma.Over.Basic

namespace CategoryTheory.Functor

open CategoryTheory

variable {C D : Type*} [Category C] [Category D] {F : C ⥤ D} {G : D ⥤ C} (A : F ⊣ G)

variable (X : C)

instance [F.Faithful] : (Over.post (X := X) F).Faithful where
  map_injective {A B} f g h := by
    ext
    exact F.map_injective (congrArg CommaMorphism.left h)

instance [F.Faithful] [F.Full] : (Over.post (X := X) F).Full where
  map_surjective {A B} f := by
    obtain ⟨a, ha⟩ := F.map_surjective f.left
    have w : a ≫ B.hom = A.hom := by
      apply F.map_injective
      simp [ha]
      apply Over.w
    use Over.homMk a
    ext
    simpa

instance [F.Full] [F.EssSurj] : (Over.post (X := X) F).EssSurj where
  mem_essImage B := by
    obtain ⟨A', ⟨e⟩⟩ := Functor.EssSurj.mem_essImage (F := F) B.left
    let f' : F.obj A' ⟶ F.obj X := e.hom ≫ B.hom
    obtain ⟨f, hf⟩ := F.map_surjective f'
    use Over.mk f
    exact ⟨Over.isoMk e⟩

instance [F.IsEquivalence] : (Over.post (X := X) F).IsEquivalence where

/-- If `F` is fully faithful, also `Over.post F` is fully faithful. -/
def FullyFaithful.over (h : F.FullyFaithful) :
    (Over.post (X := X) F).FullyFaithful where
  preimage {A B} f := Over.homMk (h.preimage f.left) <|
    h.map_injective (by simpa using Over.w f)

end CategoryTheory.Functor
