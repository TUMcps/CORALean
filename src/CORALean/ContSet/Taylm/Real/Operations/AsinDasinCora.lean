module

public import Mathlib.Data.Real.Basic

@[expose] public section

/-!
# `Taylm.asinDasinCora`: `aux_dasin` of CORA's `asin(taylm)`

`@taylm/asin.m`: `aux_dasin(k) = (k-2)^2` for `k >= 3`, `1` below.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- CORA's `aux_dasin(k)`. -/
def Taylm.asinDasinCora (k : ℕ) : ℝ := if 3 ≤ k then ((k : ℝ) - 2) ^ 2 else 1

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
