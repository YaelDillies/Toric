import Mathlib.CategoryTheory.EssentialImage

namespace CategoryTheory.Functor
variable {C D E : Type* } [Category C] [Category D] [Category E] {F : D ⥤ E} {G : C ⥤ D} {X : E}

/-- Pre-composing by an essentially surjective functor doesn't change the essential image. -/
@[simp] lemma essImage_comp_of_essSurj [G.EssSurj] : (G ⋙ F).essImage X ↔ F.essImage X where
  mp := fun ⟨Y, ⟨e⟩⟩ ↦ ⟨G.obj Y, ⟨e⟩⟩
  mpr := fun ⟨Y, ⟨e⟩⟩ ↦
    let ⟨Z, ⟨e'⟩⟩ := Functor.EssSurj.mem_essImage Y; ⟨Z, ⟨(F.mapIso e').trans e⟩⟩

end CategoryTheory.Functor
