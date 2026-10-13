import CORALean.ContSet.Taylm.Real.Operations.GlobalMin
import CORALean.ContSet.Taylm.Real.Operations.GoLowerBound

/-!
# `Taylm.cosyGo`

[1, Sec. 4]'s verified global optimizer on a model over a sub-box `X` of the normalized box:
COSY-GO's box steps with its bound of a box, and the mid-point estimate `P(p) + sup I`.

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

noncomputable def Taylm.cosyGo (T : Taylm n) (X : Fin n → ℝ × ℝ) (ε : ℝ) (ldbFuel fuel : ℕ) :
    ℝ × ℝ :=
  Taylm.globalMin (T.goLowerBound ε ldbFuel) (fun p => T.poly p + T.remSup) X fuel

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
