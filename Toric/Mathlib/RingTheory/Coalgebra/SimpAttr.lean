import Mathlib.Init
import Lean.Meta.Tactic.Simp.SimpTheorems
import Lean.Meta.Tactic.Simp.RegisterCommand
import Lean.LabelAttribute

register_simp_attr coassoc_simps

register_simp_attr coassoc_cleanup_simps
