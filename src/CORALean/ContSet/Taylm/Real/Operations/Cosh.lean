import CORALean.ContSet.Taylm.Real.Operations.Taylor
import CORALean.ContSet.Taylm.Real.Operations.ConstCoef
import Mathlib.Analysis.Complex.Trigonometric
import CORALean.ContSet.Taylm.Real.Operations.Mag

/-!
# `Taylm.cosh`

CORA's `cosh`: the expansion at the constant part; every derivative of `cosh` is `cosh` or
`sinh`, at most `cosh` of the magnitude.

The hyperbolic cosine of [1, Def. 3 (cosh)].

## References

* [1] K. Makino and M. Berz. "Taylor Models and Other Validated Functional Inclusion
      Methods". International Journal of Pure and Applied Mathematics, 4(4):379-452, 2003.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def Taylm.cosh (T : Taylm n) : Taylm n :=
  T.taylor Real.cosh T.constCoef (Real.cosh T.mag)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
