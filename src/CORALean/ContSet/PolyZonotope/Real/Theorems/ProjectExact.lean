module

public import CORALean.ContSet.PolyZonotope.Real.Operations.Project
public import CORALean.ContSet.PolyZonotope.Real.Theorems.MapExact

@[expose] public section

/-!
# `project` is exactly the coordinate

[1, Prop. 2.11] states the construction and leaves what it denotes implicit.
`project` is a `map`, so `map_exact` says it: the image of the set under the
coordinate functional, with nothing added and nothing lost.

## Inputs
* `pZ` – polynomial zonotope
* `i` – coordinate

## Hypotheses
* none

## Conclusion
* the coordinate image of the set equals the result

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


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.project_exact (pZ : PolyZonotope (Vec ℝ n)) (i : Fin n) :
    (LinearMap.proj i : Vec ℝ n →ₗ[ℝ] ℝ) '' pZ.construct = (pZ.project i).construct :=
  PolyZonotope.map_exact (LinearMap.proj i) pZ

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
