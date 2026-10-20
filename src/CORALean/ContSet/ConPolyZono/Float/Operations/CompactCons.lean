module

public import CORALean.ContSet.ConPolyZono.Float.ConPolyZono
public import CORALean.ContSet.PolyLevelSet.Float.Operations.Compact

@[expose] public section

/-!
# `ConPolyZono.compactCons`

Equal constraint exponent columns added together: the constraint's own `PolyLevelSet.compact`,
the stored value the lower rounding and the widening paid into the slack `b_error`. The
generators stand, so the ambient box is untouched.

## Inputs
* `cPZ` – constrained polynomial zonotope

## Output
* same set with equal constraint columns merged
-/

-- Authors:       Claude Opus 5, Claude Opus 5.5
-- Written:       04-September-2026
-- Last update:   19-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- CORA's merge of equal constraint columns: the constraint's own `PolyLevelSet.compact`. -/
def ConPolyZono.compactCons (cPZ : ConPolyZono 𝕋 (Vec 𝕋 n)) : ConPolyZono 𝕋 (Vec 𝕋 n) :=
  { cPZ with cons := cPZ.cons.compact, cons_eq := cPZ.cons_eq }

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
