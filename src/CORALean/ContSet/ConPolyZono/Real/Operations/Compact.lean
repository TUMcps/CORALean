import CORALean.ContSet.ConPolyZono.Real.Operations.CompactCons
import CORALean.ContSet.ConPolyZono.Real.Operations.CompactFactors
import CORALean.ContSet.ConPolyZono.Real.Operations.CompactGens

/-!
# `ConPolyZono.compact`

CORA's `@conPolyZono/compact_` at `'all'`: equal exponent columns are added
together and a column that came out zero is dropped, in the constraint matrix
as well as in the generators, and then the factors that fell out of use go.
Exact.

CORA's `compact` runs the generators, then the constraints, then the factors.
The order matters in one direction only — dropping a column can leave a
factor unused, never the reverse.
-/

-- Authors:       Tobias Ladner
-- Written:       04-September-2026
-- Last update:   05-September-2026
-- Last revision: ---

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]

/-- CORA's `compact`: the generators, then the constraints, then the factors.
The order matters in one direction only — dropping a column can leave a factor
unused, never the reverse. -/
noncomputable def ConPolyZono.compact (C : ConPolyZono α) : ConPolyZono α :=
  C.compactGens.compactCons.compactFactors

end CORALean.Real
