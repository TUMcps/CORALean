module

public import CORALean.ContSet.Conversion.Real.Theorems.PolyZonotopeConPolyZonoExact
public import CORALean.ContSet.ConPolyZono.Real.Theorems.IsCompact
public import CORALean.ContSet.Conversion.Real.Operations.PolyZonotope_to_ConPolyZono

@[expose] public section

/-!
# A polynomial zonotope is compact

A polynomial zonotope is the constrained one with no constraints
(`conPolyZono_exact`), which is compact. Compactness, not only boundedness, is
what a float polynomial zonotope inherits: its error box is compact and
`IsCompact.add` carries the property across the sum.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [NormedAddCommGroup α] [NormedSpace ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.isCompact_construct (pZ : PolyZonotope α) : IsCompact pZ.construct := by
  rw [PolyZonotope.conPolyZono_exact]
  exact pZ.conPolyZono.isCompact_construct

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
