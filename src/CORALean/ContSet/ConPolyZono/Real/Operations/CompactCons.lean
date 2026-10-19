module

public import CORALean.ContSet.ConPolyZono.Real.Operations.Basic
public import CORALean.ContSet.PolyLevelSet.Real.Operations.Compact

@[expose] public section

/-!
# `ConPolyZono.compactCons`

Equal constraint exponent columns added together and the zero columns gone: the constraint's own
`PolyLevelSet.compact`, the generators untouched. `b` stands: a merged column is exact, and a
column at exponent zero stays a column here rather than moving into the bound.
-/

-- Authors:       Claude Opus 5, Claude Opus 5.5
-- Written:       04-September-2026
-- Last update:   18-October-2026
-- Reviewed:      14-October-2026 (Tobias Ladner)
--                19-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Equal constraint exponent columns added together and the zero columns gone.
`b` stands: a merged column is exact, and a column at exponent zero stays a
column here rather than moving into the bound. -/
noncomputable def ConPolyZono.compactCons (cPZ : ConPolyZono α) : ConPolyZono α :=
  { cPZ with cons := cPZ.cons.compact, cons_eq := cPZ.cons_eq }

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
