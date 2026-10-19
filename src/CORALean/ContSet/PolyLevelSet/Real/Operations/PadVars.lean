module

public import CORALean.ContSet.PolyLevelSet.Real.PolyLevelSet
public import CORALean.ContSet.PolyZonotope.Real.Operations.PadE

@[expose] public section

/-!
# `PolyLevelSet.padVars`

`r` fresh variables after the old ones, at exponent zero in every monomial, so no row reads them:
CORA's `@levelSet/lift_` at the embedding of the old variables as the first ones.
-/

-- Authors:       Claude Opus 5.5
-- Written:       18-October-2026
-- Last update:   ---
-- Reviewed:      19-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The same rows over `n + r` variables, the last `r` read by none. -/
def PolyLevelSet.padVars (P : PolyLevelSet n) (r : ℕ) : PolyLevelSet (n + r) where
  m := P.m
  q := P.q
  A := P.A
  R := PolyZonotope.padE P.R r
  b := P.b
  op := P.op

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
