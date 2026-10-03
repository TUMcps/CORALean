import CORALean.ContSet.Taylm.Real.Operations.Taylor
import CORALean.ContSet.Taylm.Real.Operations.ConstCoef
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# `Taylm.invSqrt`

The multiplicative inverse of the square root of [1, Def. 3 (1/sqrt)]: the expansion of
`x^(-1/2)` at the constant part, the `(N+1)`-th derivative being
`(-1/2)(-1/2 - 1)⋯ x^(-1/2 - N - 1)`, largest in magnitude at the bottom of the range. The
source writes the coefficients as `(2k - 1)!! / (k! 2ᵏ)`; `descPochhammer` at `-1/2` over `k!`
is the same number with its sign.

## References

* [1] K. Makino and M. Berz. "Taylor Models and Other Validated Functional Inclusion
      Methods". International Journal of Pure and Applied Mathematics, 4(4):379-452, 2003.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def Taylm.invSqrt (T : Taylm n) : Taylm n :=
  T.taylor (fun x => x ^ (-(1 / 2) : ℝ)) T.constCoef
    (|(descPochhammer ℝ (T.maxOrder + 1)).eval (-(1 / 2))|
      * min T.constCoef T.bounds.1 ^ (-(1 / 2) - (T.maxOrder + 1 : ℕ) : ℝ))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
