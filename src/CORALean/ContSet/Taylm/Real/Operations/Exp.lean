module

public import CORALean.ContSet.Taylm.Real.Operations.Taylor
public import CORALean.ContSet.Taylm.Real.Operations.Basic
public import Mathlib.Analysis.Complex.Exponential

@[expose] public section

/-!
# `Taylm.exp`

CORA's `exp`: the expansion at the constant part, every derivative `exp`, so the Lagrange
derivative is bounded by `exp` at the top of the range.

The exponential of [1, Def. 3 (exp)] at `k = n`, the source's eq. (2.2), its Lagrange term
bounded in magnitude rather than as the interval product of eq. (2.4).

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

noncomputable def Taylm.exp (T : Taylm n) : Taylm n :=
  T.taylor Real.exp T.constCoef (Real.exp (max T.constCoef T.bounds.2))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
