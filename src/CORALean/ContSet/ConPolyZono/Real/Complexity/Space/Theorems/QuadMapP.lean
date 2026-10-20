module

public import CORALean.ContSet.ConPolyZono.Real.Operations.QuadMap
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Tactic.Positivity

@[expose] public section

/-!
# `ConPolyZono.quadMap`'s counts

`quadMap` is `quadMapDep` run on `dependent`: the factor and dependent-generator counts are
`dependent`'s own, and the constraint counts `m` and `q` carry straight through, since the
constraint system reads none of the enclosing polynomial zonotope; `rfl` by unfolding. The
dependent-generator count is `O(m ^ 2)` for a family of sets whose combined generator count grows
as `m`: `quadMap_h` reduces the left side to `(m+1)*(m+1)`, which `4 * m ^ 2` dominates for `m ≥
1`.

## Inputs
* `Q` – family of quadratic forms
* `cPZ` – constrained polynomial zonotope

## Hypotheses
* none

## Conclusion
* the factor count is the operand's factors plus independent generators
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   13-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n k : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The `p` count of `quadMap`'s result. -/
theorem ConPolyZono.quadMap_p (Q : Fin k → Mat ℝ n n) (cPZ : ConPolyZono (Vec ℝ n)) :
    (ConPolyZono.quadMap Q cPZ).p = cPZ.p + cPZ.qI := rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
