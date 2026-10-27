module

public import CORALean.ContSet.PolyZonotope.Real.Operations.Map
public import Mathlib.LinearAlgebra.Pi

@[expose] public section

/-!
# `PolyZonotope.project`

CORA's `@polyZonotope/project` and [1, Prop. 2.11]: one coordinate of the set, which is `map`
at that coordinate's functional; the exponent matrix and both factor counts are untouched,
because reading off a coordinate is linear. Nothing in this tree calls it: `evalPoly` is
coordinatewise by construction, so the split of [1, Alg. 1] into one-dimensional sets never
happens here. It is still the representation's operation, and `project_exact` says so.

## Inputs
* `pZ` – polynomial zonotope
* `i` – coordinate

## Output
* one-dimensional polynomial zonotope of that coordinate

## References

* [1] [T. Ladner and M. Althoff. "Automatic Abstraction Refinement in Neural Network Verification
      using Sensitivity Analysis". Proceedings of the 26th ACM International Conference on Hybrid
      Systems: Computation and Control,
      2023.](../../../../../../references/2023/ladner-hscc-abstraction-refinement.md)
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
