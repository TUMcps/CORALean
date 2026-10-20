module

public import CORALean.ContSet.ConPolyZono.Real.Operations.CompactCons
public import CORALean.ContSet.ConPolyZono.Real.Operations.CompactFactors
public import CORALean.ContSet.ConPolyZono.Real.Operations.CompactGens

@[expose] public section

/-!
# `ConPolyZono.compact`

CORA's `@conPolyZono/compact_` at `'all'`: equal exponent columns are added
together and a column that came out zero is dropped, in the constraint matrix
as well as in the generators, and then the factors that fell out of use go.
Exact.

CORA's `compact` runs the generators, then the constraints, then the factors.
The order matters in one direction only — dropping a column can leave a
factor unused, never the reverse.

## Inputs
* `cPZ` – constrained polynomial zonotope

## Output
* same set with equal columns merged and unused factors dropped
-/

-- Authors:       Claude Opus 5
-- Written:       04-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- CORA's `compact`: the generators, then the constraints, then the factors.
The order matters in one direction only — dropping a column can leave a factor
unused, never the reverse. -/
noncomputable def ConPolyZono.compact (cPZ : ConPolyZono α) : ConPolyZono α :=
  cPZ.compactGens.compactCons.compactFactors

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
