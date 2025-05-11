import Mathlib.CategoryTheory.Monoidal.Comon_
import Toric.Mathlib.CategoryTheory.Monoidal.Mon_
import Toric.Mathlib.CategoryTheory.Monoidal.NaturalTransformation
import Toric.Mathlib.CategoryTheory.Monoidal.Opposite

open CategoryTheory

universe v₁ v₂ v₃ u₁ u₂ u₃
variable (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C]

open Functor LaxMonoidal OplaxMonoidal

@[simps!]
def monOpEquivComonOp : Mon_ Cᵒᵖ ≌ (Comon_ C)ᵒᵖ := (Comon_.Comon_EquivMon_OpOp C).symm.rightOp

@[simps!]
noncomputable def comonOpEquivMonOp : Comon_ Cᵒᵖ ≌ (Mon_ C)ᵒᵖ :=
  (Comon_.Comon_EquivMon_OpOp Cᵒᵖ).trans <| .op (opOpEquivalence C).mapMon

section BraidedCategory
variable [BraidedCategory C]

instance : (monOpEquivComonOp C).functor.OplaxMonoidal := sorry
instance : (monOpEquivComonOp C).inverse.OplaxMonoidal := sorry

end BraidedCategory

namespace CategoryTheory
variable {C}
  {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]
  {E : Type u₃} [Category.{v₃} E] [MonoidalCategory E]
  {F F' : C ⥤ D} {G : D ⥤ E}

namespace Functor
section OplaxMonoidal
variable [F.OplaxMonoidal] [F'.OplaxMonoidal] [G.OplaxMonoidal] (X Y : C) [Mon_Class X]
  [Mon_Class Y] (f : X ⟶ Y) [IsMon_Hom f]

/-- The identity functor is also the identity on comonoid objects. -/
@[simps!]
noncomputable def mapComonIdIso : mapComon (𝟭 C) ≅ 𝟭 (Comon_ C) :=
  NatIso.ofComponents fun X ↦ Comon_.mkIso (.refl _)

/-- The composition functor is also the composition on comonoid objects. -/
@[simps!]
noncomputable def mapComonCompIso : (F ⋙ G).mapComon ≅ F.mapComon ⋙ G.mapComon :=
  NatIso.ofComponents fun X ↦ Comon_.mkIso (.refl _)

protected instance Faithful.mapComon [F.Faithful] : F.mapComon.Faithful where
  map_injective {_X _Y} _f _g hfg := Comon_.Hom.ext <| map_injective congr(($hfg).hom)

-- /-- Natural transformations between functors lift to monoid objects. -/
-- @[simps!]
-- noncomputable def mapComonNatTrans (f : F ⟶ F') [NatTrans.IsOplaxMonoidal f] :
--     F.mapComon ⟶ F'.mapComon where
--   app X := .mk (f.app _)

-- /-- Natural isomorphisms between functors lift to monoid objects. -/
-- @[simps!]
-- noncomputable def mapComonNatIso (e : F ≅ F') [NatTrans.IsOplaxMonoidal e.hom] :
--     F.mapComon ≅ F'.mapComon :=
--   NatIso.ofComponents fun X ↦ Comon_.mkIso (e.app _)

end OplaxMonoidal

section Monoidal
variable [F.Monoidal]

-- attribute [local instance] obj.instComon_Class

-- protected instance Full.mapComon [F.Full] [F.Faithful] : F.mapComon.Full where
--   map_surjective {X Y} f :=
--     let ⟨g, hg⟩ := F.map_surjective f.hom
--     ⟨{
--       hom := g
--       one_hom := F.map_injective <| by simpa [← hg, cancel_epi] using f.one_hom
--       mul_hom := F.map_injective <| by simpa [← hg, cancel_epi] using f.mul_hom
--     }, Comon_.Hom.ext hg⟩

-- instance FullyFaithful.isComon_Hom_preimage (hF : F.FullyFaithful) {X Y : C}
--     [Comon_Class X] [Comon_Class Y] (f : F.obj X ⟶ F.obj Y) [IsComon_Hom f] :
--     IsComon_Hom (hF.preimage f) where
--   one_hom := hF.map_injective <| by simp [← obj.η_def_assoc, ← obj.η_def, ← cancel_epi (ε F)]
--   mul_hom := hF.map_injective <| by
--     simp [← obj.μ_def_assoc, ← obj.μ_def, ← μ_natural_assoc, ← cancel_epi (LaxMonoidal.μ F ..)]

-- /-- If `F : C ⥤ D` is a fully faithful monoidal functor, then `Mon(F) : Mon C ⥤ Mon D` is fully
-- faithful too. -/
-- protected def FullyFaithful.mapComon (hF : F.FullyFaithful) : F.mapComon.FullyFaithful where
--   preimage {X Y} f := .mk' <| hF.preimage f.hom

end Monoidal

-- variable (C D) in
-- /-- `mapComon` is functorial in the lax monoidal functor. -/
-- @[simps] -- Porting note: added this, not sure how it worked previously without.
-- def mapComonFunctor : LaxMonoidalFunctor C D ⥤ Comon_ C ⥤ Comon_ D where
--   obj F := F.mapComon
--   map α := { app := fun A => { hom := α.hom.app A.X } }
--   map_comp _ _ := rfl

end Functor

open Functor

-- namespace Adjunction
-- variable {F : C ⥤ D} {G : D ⥤ C} (a : F ⊣ G) [F.Monoidal] [G.OplaxMonoidal] [a.IsOplaxMonoidal]

-- /-- An adjunction of monoidal functors lifts to an adjunction of their lifts to monoid objects.
-- -/
-- @[simps] noncomputable def mapComon : F.mapComon ⊣ G.mapComon where
--   unit := mapComonIdIso.inv ≫ mapComonNatTrans a.unit ≫ mapComonCompIso.hom
--   counit := mapComonCompIso.inv ≫ mapComonNatTrans a.counit ≫ mapComonIdIso.hom

-- end Adjunction

-- namespace Equivalence

-- /-- An equivalence of categories lifts to an equivalence of their monoid objects. -/
-- @[simps]
-- noncomputable def mapComon (e : C ≌ D) [e.functor.Monoidal] [e.inverse.Monoidal] [e.IsMonoidal] :
--     Comon_ C ≌ Comon_ D where
--   functor := e.functor.mapComon
--   inverse := e.inverse.mapComon
--   unitIso := mapComonIdIso.symm ≪≫ mapComonNatIso e.unitIso ≪≫ mapComonCompIso
--   counitIso := mapComonCompIso.symm ≪≫ mapComonNatIso e.counitIso ≪≫ mapComonIdIso

-- end CategoryTheory.Equivalence
end CategoryTheory
