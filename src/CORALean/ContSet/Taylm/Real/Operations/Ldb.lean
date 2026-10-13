module

public import CORALean.ContSet.Taylm.Real.Operations.LdbLoop

@[expose] public section

/-!
# `Taylm.ldb`

The lower bound of a model's minimum over the normalized box by the linear dominated bounder,
[1, Sec. 2], from the whole box. The upper bound of the maximum is the same of `-T`.

## References

* [1] K. Makino and M. Berz. "Verified Global Optimization with Taylor Model-based Range
      Bounders". Transactions on Computers, 11(4):1611-1618, 2005.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def Taylm.ldb (T : Taylm n) (ε : ℝ) (fuel : ℕ) : ℝ :=
  Taylm.ldbLoop T ε fuel fun _ => (-1, 1)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
