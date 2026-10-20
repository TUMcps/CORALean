module

public import CORALean.ContSet.PolyZonotope.Real.PolyZonotope

@[expose] public section

/-!
# The exponent matrix widened to match `extG`

Split out of `QuadMap.lean` (issue #62): shared with `Mul.lean` in this
directory and with the float layer's own `quadMap` and `mul`, all outside
this file.

## Inputs
* `pZ` – polynomial zonotope

## Output
* exponent matrix with a zero column for the center
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The exponent matrix widened to match, the center's column being zero — its
monomial is `1`, which is what the center needs to be. -/
def PolyZonotope.extE (pZ : PolyZonotope α) : Fin pZ.p → Fin (pZ.h + 1) → ℕ :=
  fun k => Fin.cons 0 (pZ.E k)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
