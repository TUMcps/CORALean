module

public import CORALean.ContSet.ConZonotope.Real.ConZonotope
public import CORALean.ContSet.HPolytope.Real.Instances
public import CORALean.ContSet.Interval.Real.Operations.Basic
public import CORALean.ContSet.StarSet.Real.StarSet

@[expose] public section

/-!
# A constrained zonotope as a star set

CORA's `conversionConZonoStarSet`: the center and the generators as they are, the coefficient box
`[-1, 1]`, and the constraint polytope on the factors as the predicate, as it is.

## Inputs
* `cZ` – constrained zonotope

## Output
* halfspace-predicate star set of the constrained zonotope
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   19-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def ConZonotope.starSet (cZ : ConZonotope (Vec ℝ n)) : StarSet ℋ𝒫 n where
  m := cZ.h
  c := cZ.c
  G := fun i k => cZ.G k i
  dom := Interval.unit cZ.h
  pred := cZ.P

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
