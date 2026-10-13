import CORALean.ContSet.PolyZonotope.Real.Operations.Map
import Mathlib.LinearAlgebra.Pi

/-!
# `PolyZonotope.project`

CORA's `@polyZonotope/project` and [1, Prop. 2.11]: one coordinate of the set,
which is `map` at that coordinate's functional — the exponent matrix and both
factor counts are untouched, exactly as [1] writes it, because reading off a
coordinate is linear.

Nothing in this tree calls it. `evalPoly` is coordinatewise by construction,
`mul` multiplying entrywise, so the split of [1, Alg. 1] into one-dimensional
sets and the recombination afterwards never happen here. It is still the
representation's operation, and `project_exact` is what says so.

## References

* [1] T. Ladner and M. Althoff. "Automatic Abstraction Refinement in Neural
      Network Verification using Sensitivity Analysis". HSCC 2023.
-/

-- Authors:       Claude Opus 5
-- Written:       12-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The set's `i`-th coordinate, as a one-dimensional polynomial zonotope. -/
def PolyZonotope.project (pZ : PolyZonotope (Vec ℝ n)) (i : Fin n) : PolyZonotope ℝ :=
  pZ.map (LinearMap.proj i)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
