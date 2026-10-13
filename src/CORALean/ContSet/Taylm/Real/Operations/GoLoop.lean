module

public import CORALean.ContSet.Taylm.Real.Operations.GoStep

@[expose] public section

/-!
# COSY-GO's box steps

[1, Sec. 4]: box steps until `fuel` runs out.

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

noncomputable def Taylm.goLoop (lb : (Fin n → ℝ × ℝ) → ℝ) (ub : Vec ℝ n → ℝ) :
    ℕ → List (Fin n → ℝ × ℝ) × ℝ → List (Fin n → ℝ × ℝ) × ℝ
  | 0, st => st
  | fuel + 1, st => Taylm.goLoop lb ub fuel (Taylm.goStep lb ub st)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
