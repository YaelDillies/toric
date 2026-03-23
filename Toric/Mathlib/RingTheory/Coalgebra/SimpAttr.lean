module

public import Mathlib.Init
public meta import Lean.LabelAttribute -- TODO: `registerLabelAttr` should be marked `meta`
public import Lean.LabelAttribute
public import Lean.Meta.Tactic.Simp

register_simp_attr coassoc_simps

register_simp_attr coassoc_cleanup_simps
