import CORALean.ContSet.Taylm.Real.Taylm
import CORALean.ContSet.Interval.Real.Operations.MulLo
import CORALean.ContSet.Interval.Real.Operations.MulHi

/-!
# `Taylm.smul`

CORA's `times` and `mtimes` by a number (`aux_s_times_td`): the coefficients and the
remainder scaled. The remainder is the interval product, so a negative factor swaps its
ends.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Taylm.smul (a : ℝ) (T : Taylm n) : Taylm n :=
  ⟨T.terms.map fun b => (a * b.1, b.2), Interval.mulLo a a T.remInf T.remSup,
    Interval.mulHi a a T.remInf T.remSup, T.maxOrder⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
