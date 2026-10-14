module

public import CORALean.ContSet.Taylm.Real.Operations.AsinDasinCora

@[expose] public section

/-!
# `Taylm.asinFactor1Cora`: the running `factor1` of CORA's `asin(taylm)`

`@taylm/asin.m` multiplies `factor1` by `aux_dasin(i)` at every odd step `i` of its loop.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The value of `factor1` after step `i`. -/
def Taylm.asinFactor1Cora : ℕ → ℝ
  | 0 => 1
  | i + 1 => if (i + 1) % 2 = 1 then Taylm.asinFactor1Cora i * Taylm.asinDasinCora (i + 1)
      else Taylm.asinFactor1Cora i

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
