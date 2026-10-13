import CORALean.ContSet.Taylm.Real.Operations.Taylor
import CORALean.ContSet.Taylm.Real.Operations.ConstCoef
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# `Taylm.sqrt`

CORA's `sqrt`: the expansion at the constant part, the `(N+1)`-th derivative of `x^(1/2)`
being `(1/2)(1/2 - 1)⋯ x^(1/2 - N - 1)`, largest in magnitude at the bottom of the range.

The square root of [1, Def. 3 (sqrt)], under its condition that the range is positive.

## References

* [1] K. Makino and M. Berz. "Taylor Models and Other Validated Functional Inclusion
      Methods". International Journal of Pure and Applied Mathematics, 4(4):379-452, 2003.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def Taylm.sqrt (T : Taylm n) : Taylm n :=
  T.taylor Real.sqrt T.constCoef
    (|(descPochhammer ℝ (T.maxOrder + 1)).eval (1 / 2)|
      * min T.constCoef T.bounds.1 ^ ((1 / 2 : ℝ) - (T.maxOrder + 1 : ℕ)))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
