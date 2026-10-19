module

public import CORALean.ContSet.Interval.Real.Operations.Basic
public import CORALean.ContSet.PolyLevelSet.Real.PolyLevelSet
public import CORALean.ContSet.PolyZonotope.Real.Operations.PadE

@[expose] public section

/-!
# `PolyLevelSet.padVars`

`r` fresh variables after the old ones, ranging over the box `D` and at exponent zero in every
monomial, so no row reads them: CORA's `@levelSet/lift_` at the embedding of the old variables as
the first ones, the new box appended to the old.

## Inputs
* `P` – polynomial level set
* `r` – number of fresh variables
* `D` – box of the fresh variables

## Output
* the level set with `r` unused variables appended
-/

-- Authors:       Claude Opus 5.5
-- Written:       18-October-2026
-- Last update:   19-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The same rows over `n + r` variables, the last `r` in `D` and read by none. -/
def PolyLevelSet.padVars (P : PolyLevelSet n) {r : ℕ} (D : Interval (Vec ℝ r)) :
    PolyLevelSet (n + r) where
  m := P.m
  q := P.q
  A := P.A
  R := PolyZonotope.padE P.R r
  b := P.b
  op := P.op
  dom := P.dom.append D

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
