module

public import CORALean.ContSet.ConZonotope.Float.ConZonotope
public import CORALean.ContSet.HPolytope.Float.Operations.ContainsOrigin

@[expose] public section

/-!
# `ConZonotope.zeroFeasible`: the center is a point of the set

A test on the constraint rows alone that coefficients `0` meet them, which is the constraint's own
`HPolytope.containsOrigin` (#174): every inequality's bound with its slack is at least `0` and
every equality's right-hand side is within its slack of `0`. Then the center is a point of the
nominal part, so the set is nonempty (`zeroFeasible_nonempty`). Sufficient, not necessary:
`false` says only that the center may be outside.

## Inputs
* `cZ` – float constrained zonotope

## Output
* whether the zero coefficient vector meets the constraints
-/

-- Authors:       Claude Opus 5.5, Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   19-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Whether coefficients `0` meet every row. -/
def ConZonotope.zeroFeasible (cZ : ConZonotope 𝕋 (Vec 𝕋 n)) : Bool := cZ.P.containsOrigin

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
