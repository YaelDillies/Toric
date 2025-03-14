import Mathlib.RingTheory.Finiteness.Defs

variable {G : Type*} [AddCommGroup G]

instance [AddMonoid.FG G] : Module.Finite ℤ G :=
  Module.Finite.iff_addGroup_fg.mpr <| AddGroup.fg_iff_addMonoid_fg.mpr inferInstance
