module

public import CORALean.ContSet.Taylm.Real.Operations.Taylor
public import CORALean.ContSet.Taylm.Real.Operations.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

@[expose] public section

/-!
# `Taylm.log`

CORA's `log`: the expansion at the constant part, `|log⁽ᴺ⁺¹⁾ ξ| = N! / ξᴺ⁺¹`, largest at the
bottom of the range. Meaningful where that bottom is positive, which `LogOuter` assumes as
CORA's `CORA:outOfDomain` check does.

The logarithm of [1, Def. 3 (log)], eq. (2.5), under its condition that the range is positive.

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

noncomputable def Taylm.log (T : Taylm n) : Taylm n :=
  T.taylor Real.log T.constCoef
    ((T.maxOrder.factorial : ℝ) / min T.constCoef T.bounds.1 ^ (T.maxOrder + 1))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
