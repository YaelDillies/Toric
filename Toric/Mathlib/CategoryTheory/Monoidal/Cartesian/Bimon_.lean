/-
Copyright (c) 2025 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.CategoryTheory.Monoidal.Cartesian.Comon_
import Mathlib.CategoryTheory.Monoidal.Bimon_

/-!
# Bimonoid objects in a cartesian monoidal category

The category of bimonoid objects in a cartesian monoidal category is equivalent
to the category of monoid objects, via the forgetful functor.
-/

open CategoryTheory MonoidalCategory Limits

universe v u

noncomputable section

variable (C : Type u) [Category.{v} C] [MonoidalCategory C]

variable [BraidedCategory C]

instance : HasTerminal (Mon_ C) := sorry
instance : HasBinaryProducts (Mon_ C) := sorry

-- /--
-- The functor from a cartesian monoidal category to comonoids in that category,
-- equipping every object with the diagonal map as a comultiplication.
-- -/
-- def cartesianBimon_ : Mon_ C ⥤ Bimon_ C := by
--   unfold Bimon_; exact cartesianComon_ (Mon_ C)

variable {C}

-- /--
-- Every comonoid object in a cartesian monoidal category is equivalent to
-- the canonical comonoid structure on the underlying object.
-- -/
-- @[simps] def isoCartesianBimon_ (A : Bimon_ C) : A ≅ (cartesianBimon_ C).obj A.X :=
--   { hom := { hom := 𝟙 _ }
--     inv := { hom := 𝟙 _ } }

-- /--
-- The category of comonoid objects in a cartesian monoidal category is equivalent
-- to the category itself, via the forgetful functor.
-- -/
-- @[simps!] def bimonEquivMon : Bimon_ C ≌ Mon_ C := comonEquiv
