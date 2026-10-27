module

public import CORALean.ContSet.Taylm.Real.Operations.Taylor
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

/-!
# `Taylm.sqrt`

CORA's `sqrt`: the expansion at the constant part, the `(N+1)`-th derivative of `x^(1/2)`
being `(1/2)(1/2 - 1)⋯ x^(1/2 - N - 1)`, largest in magnitude at the bottom of the range.

The square root of [1, Def. 3 (sqrt)], under its condition that the range is positive.

## Inputs
* `T` – Taylor model

## Output
* Taylor model of the square root of the argument

## References

* [1] [K. Makino and M. Berz. "Taylor Models and Other Validated Functional Inclusion Methods".
      International Journal of Pure and Applied Mathematics,
      2003.](../../../../../../references/2003/makino-ijpam-taylor-models.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def Taylm.sqrt (T : Taylm n) : Taylm n :=
  T.taylor Real.sqrt T.constCoef
    (|(descPochhammer ℝ (T.maxOrder + 1)).eval (1 / 2)|
      * min T.constCoef T.bounds.inf ^ ((1 / 2 : ℝ) - (T.maxOrder + 1 : ℕ)))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
