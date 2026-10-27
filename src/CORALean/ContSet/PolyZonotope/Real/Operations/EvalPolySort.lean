module

public import CORALean.ContSet.PolyZonotope.Real.Operations.EvalPolySortP

@[expose] public section

/-!
# `PolyZonotope.evalPolySort`

[1, Alg. 2]: the polynomial evaluated by powers rather than by Horner's rule: `PZ^i` computed by
repeated `sq`, each sorted and merged, and the `o` terms summed with `sortPlus`. Coefficients
lowest degree first and one vector per degree, as `evalPoly` takes them. `evalPoly` reaches the
same value by a different route; this one keeps the exponent matrix sorted throughout and never
calls `compact`. The independent block is not part of the claim: [1, Alg. 2] assumes it empty,
and a caller who needs those coefficients to count runs `dependent` on `pZ` first.

## Inputs
* `pZ` – polynomial zonotope
* `coeffs` – coefficient vectors

## Output
* polynomial zonotope of the polynomial by the sorted algorithm

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

/-- [1, Alg. 2], coefficients lowest degree first. -/
noncomputable def PolyZonotope.evalPolySort (pZ : PolyZonotope (Vec ℝ n))
    (coeffs : List (Vec ℝ n)) : PolyZonotope (Vec ℝ n) := (pZ.evalPolySortP coeffs).1

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
