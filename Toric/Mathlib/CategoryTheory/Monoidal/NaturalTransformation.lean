/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.CategoryTheory.Adjunction.FullyFaithful
import Mathlib.CategoryTheory.Monoidal.Functor
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# Monoidal natural transformations

Natural transformations between (Oplax) monoidal functors must satisfy
an additional compatibility relation with the tensorators:
`F.δ X Y ≫ app (X ⊗ Y) = (app X ⊗ app Y) ≫ G.δ X Y`.

-/

open CategoryTheory

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

open CategoryTheory.Category

open CategoryTheory.Functor

namespace CategoryTheory

open MonoidalCategory

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
  {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]
  {E : Type u₃} [Category.{v₃} E] [MonoidalCategory E]
  {E' : Type u₄} [Category.{v₄} E'] [MonoidalCategory E']

variable {F F₁ F₂ F₃ : C ⥤ D} {G G₁ G₂ : D ⥤ E} {H H₁ H₂ : E ⥤ E'}
  [F.OplaxMonoidal] [F₁.OplaxMonoidal] [F₂.OplaxMonoidal] [F₃.OplaxMonoidal]
  [G.OplaxMonoidal] [G₁.OplaxMonoidal] [G₂.OplaxMonoidal]
  [H.OplaxMonoidal] [H₁.OplaxMonoidal] [H₂.OplaxMonoidal] (τ : F₁ ⟶ F₂)

namespace NatTrans

open Functor.OplaxMonoidal

/-- A natural transformation between oplax monoidal functors is monoidal if it satisfies
`η F ≫ τ.app (𝟙_ C) = η G` and `δ F X Y ≫ app (X ⊗ Y) = (app X ⊗ app Y) ≫ δ G X Y`. -/
class IsOplaxMonoidal : Prop where
  unit : τ.app (𝟙_ C) ≫ η F₂ = η F₁ := by aesop_cat
  tensor (X Y : C) : τ.app (X ⊗ Y) ≫ δ F₂ _ _ = δ F₁ _ _ ≫ (τ.app X ⊗ τ.app Y) := by aesop_cat

namespace IsOplaxMonoidal

attribute [reassoc (attr := simp)] unit tensor

instance id : IsOplaxMonoidal (𝟙 F₁) where

instance comp (τ' : F₂ ⟶ F₃) [IsOplaxMonoidal τ] [IsOplaxMonoidal τ'] :
    IsOplaxMonoidal (τ ≫ τ') where

instance hcomp (τ' : G₁ ⟶ G₂) [IsOplaxMonoidal τ] [IsOplaxMonoidal τ'] :
    IsOplaxMonoidal (τ ◫ τ') where
  unit := sorry
  tensor X Y := sorry

instance : IsOplaxMonoidal F.leftUnitor.hom where
instance : IsOplaxMonoidal F.rightUnitor.hom where
instance : IsOplaxMonoidal (F.associator G H).hom where

end IsOplaxMonoidal

instance {F G : C ⥤ D} {H K : C ⥤ E} (α : F ⟶ G) (β : H ⟶ K)
    [F.OplaxMonoidal] [G.OplaxMonoidal] [IsOplaxMonoidal α]
    [H.OplaxMonoidal] [K.OplaxMonoidal] [IsOplaxMonoidal β] :
    IsOplaxMonoidal (NatTrans.prod' α β) where
  unit := by
    ext
    · rw [prod_comp_fst, prod'_η_fst, prod'_η_fst, prod'_app_fst, IsOplaxMonoidal.unit]
    · rw [prod_comp_snd, prod'_η_snd, prod'_η_snd, prod'_app_snd, IsOplaxMonoidal.unit]
  tensor X Y := by
    ext
    · simp only [prod_comp_fst, prod'_δ_fst, prod'_app_fst,
        prodMonoidal_tensorHom, IsOplaxMonoidal.tensor]
    · simp only [prod_comp_snd, prod'_δ_snd, prod'_app_snd,
        prodMonoidal_tensorHom, IsOplaxMonoidal.tensor]

end NatTrans

namespace Iso

variable (e : F₁ ≅ F₂) [NatTrans.IsOplaxMonoidal e.hom]

instance : NatTrans.IsOplaxMonoidal e.inv where
  unit := by rw [← NatTrans.IsOplaxMonoidal.unit (τ := e.hom), ← assoc, inv_hom_id_app, id_comp]
  tensor X Y := by
    rw [← cancel_epi (e.hom.app (X ⊗ Y)), ← assoc, ← assoc, hom_inv_id_app, id_comp,
      NatTrans.IsOplaxMonoidal.tensor]
    sorry

end Iso

-- namespace Adjunction

-- variable {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)

-- open Functor LaxMonoidal OplaxMonoidal Monoidal

-- namespace IsOplaxMonoidal

-- variable [F.Monoidal] [G.OplaxMonoidal] [adj.IsMonoidal]

-- instance : NatTrans.IsOplaxMonoidal adj.unit where
--   unit := by
--     dsimp
--     rw [id_comp, ← unit_app_unit_comp_map_η adj, assoc, Monoidal.map_η_η]
--     dsimp
--     rw [comp_id]
--   tensor X Y := by
--     dsimp
--     rw [← unit_app_tensor_comp_map_δ_assoc, id_comp, Monoidal.map_δ_δ, comp_id]

-- instance : NatTrans.IsOplaxMonoidal adj.counit where
--   unit := by
--     dsimp
--     rw [assoc, map_η_comp_counit_app_unit adj, η_η]
--   tensor X Y := by
--     dsimp
--     rw [assoc, map_δ_comp_counit_app_tensor, δ_δ_assoc, comp_id]

-- end IsOplaxMonoidal

-- namespace Equivalence

-- variable (e : C ≌ D) [e.functor.Monoidal] [e.inverse.Monoidal] [e.IsOplaxMonoidal]

-- instance : NatTrans.IsOplaxMonoidal e.unit :=
--   inferInstanceAs (NatTrans.IsOplaxMonoidal e.toAdjunction.unit)

-- instance : NatTrans.IsOplaxMonoidal e.counit :=
--   inferInstanceAs (NatTrans.IsOplaxMonoidal e.toAdjunction.counit)

-- end Equivalence

-- end Adjunction

-- namespace OplaxMonoidalFunctor

-- /-- The type of monoidal natural transformations between (bundled) Oplax monoidal functors. -/
-- structure Hom (F G : OplaxMonoidalFunctor C D) where
--   /-- the natural transformation between the underlying functors -/
--   hom : F.toFunctor ⟶ G.toFunctor
--   IsOplaxMonoidal : NatTrans.IsOplaxMonoidal hom := by infer_instance

-- attribute [instance] Hom.IsOplaxMonoidal

-- instance : Category (OplaxMonoidalFunctor C D) where
--   Hom := Hom
--   comp α β := ⟨α.1 ≫ β.1, by have := α.2; have := β.2; infer_instance⟩
--   id _ := ⟨𝟙 _, inferInstance⟩

-- @[simp]
-- lemma id_hom (F : OplaxMonoidalFunctor C D) : Hom.hom (𝟙 F) = 𝟙 _ := rfl

-- @[reassoc, simp]
-- lemma comp_hom {F G H : OplaxMonoidalFunctor C D} (α : F ⟶ G) (β : G ⟶ H) :
--     (α ≫ β).hom = α.hom ≫ β.hom := rfl

-- @[ext]
-- lemma hom_ext {F G : OplaxMonoidalFunctor C D} {α β : F ⟶ G} (h : α.hom = β.hom) : α = β := by
--   cases α; cases β; subst h; rfl

-- /-- Constructor for morphisms in the category `OplaxMonoidalFunctor C D`. -/
-- @[simps]
-- def homMk {F G : OplaxMonoidalFunctor C D} (f : F.toFunctor ⟶ G.toFunctor)
--     [NatTrans.IsOplaxMonoidal f] :
--     F ⟶ G := ⟨f, inferInstance⟩

-- /-- Constructor for isomorphisms in the category `OplaxMonoidalFunctor C D`. -/
-- @[simps]
-- def isoMk {F G : OplaxMonoidalFunctor C D} (e : F.toFunctor ≅ G.toFunctor)
--     [NatTrans.IsOplaxMonoidal e.hom] :
--     F ≅ G where
--   hom := homMk e.hom
--   inv := homMk e.inv

-- open Functor.OplaxMonoidal

-- /-- Constructor for isomorphisms between Oplax monoidal functors. -/
-- @[simps!]
-- def isoOfComponents {F G : OplaxMonoidalFunctor C D} (e : ∀ X, F.obj X ≅ G.obj X)
--     (naturality : ∀ {X Y : C} (f : X ⟶ Y), F.map f ≫ (e Y).hom = (e X).hom ≫ G.map f := by
--       aesop_cat)
--     (unit : η F.toFunctor ≫ (e (𝟙_ C)).hom = η G.toFunctor := by aesop_cat)
--     (tensor : ∀ X Y, δ F.toFunctor X Y ≫ (e (X ⊗ Y)).hom =
--       ((e X).hom ⊗ (e Y).hom) ≫ δ G.toFunctor X Y := by aesop_cat) :
--     F ≅ G :=
--   @isoMk _ _ _ _ _ _ _ _ (NatIso.ofComponents e naturality) (by constructor <;> assumption)

-- end OplaxMonoidalFunctor

end CategoryTheory
