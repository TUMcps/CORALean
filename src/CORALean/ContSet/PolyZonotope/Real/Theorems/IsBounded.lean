module

public import CORALean.ContSet.Conversion.Real.Theorems.PolyZonotopeConPolyZonoExact
public import CORALean.ContSet.ConPolyZono.Real.Theorems.IsCompact
public import CORALean.ContSet.Conversion.Real.Operations.PolyZonotope_to_ConPolyZono

@[expose] public section

/-!
# A polynomial zonotope is bounded

CORA's `isBounded` is `true`. A polynomial zonotope is the constrained one with no
constraints (`conPolyZono_exact`), which is compact.

## Inputs
* `pZ` – polynomial zonotope

## Hypotheses
* none

## Conclusion
* the set is bounded
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [NormedAddCommGroup α] [NormedSpace ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.isBounded_construct (pZ : PolyZonotope α) :
    Bornology.IsBounded pZ.construct := by
  rw [PolyZonotope.conPolyZono_exact]
  exact pZ.conPolyZono.isCompact_construct.isBounded

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
