import CORALean.ContSet.PolyZonotope.Real.Operations.EvalPolySort

/-!
# The factor count [1, Alg. 2] keeps

`evalPolyFactorCount`'s counterpart: the `p`-proof read off the paired
recursion, so that a caller stating a point equation has a cast to write it
with.

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


-- =======================================  MAIN THEOREM  ======================================= --

/-- The shared factor count `evalPolySort` never leaves. -/
theorem PolyZonotope.evalPolySort_p (pZ : PolyZonotope (Vec ℝ n)) (coeffs : List (Vec ℝ n)) :
    (pZ.evalPolySort coeffs).p = pZ.p := (pZ.evalPolySortP coeffs).2

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
