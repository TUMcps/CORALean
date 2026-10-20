module

public import CORALean.ContSet.ConPolyZono.Real.Operations.Dependent
public import CORALean.ContSet.ConPolyZono.Real.Operations.QuadMapDep

@[expose] public section

/-!
# `ConPolyZono.quadMap`

CORA's `@conPolyZono/quadMap`: `quadMapDep` run on `dependent`, exactly as
`PolyZonotope.quadMap` does and for the same reason — the expansion is stated
on a set whose coefficients are all dependent. Here `dependent` also widens
the constraints with zero rows for the fresh factors, which is what keeps the
two arrangements in step.

## Inputs
* `Q` – family of quadratic forms
* `cPZ` – constrained polynomial zonotope

## Output
* image under the quadratic map
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n k : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def ConPolyZono.quadMap (Q : Fin k → Mat ℝ n n) (cPZ : ConPolyZono (Vec ℝ n)) :
    ConPolyZono (Vec ℝ k) :=
  ConPolyZono.quadMapDep Q cPZ.dependent

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
