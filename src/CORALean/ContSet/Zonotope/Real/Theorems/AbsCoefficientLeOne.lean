module

public import CORALean.ContSet.Zonotope.Real.Definitions.Coefficient

@[expose] public section

/-!
# The coefficient the unit ball allows

Half of what makes `coefficient` a witness: whatever it returns is admissible as
a zonotope coefficient. `MulCoefficient` is the other half, that it hits the
target.
-/

-- Authors:       Claude Opus 5
-- Written:       16-August-2026
-- Last update:   04-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.abs_coefficient_le_one {R D : ℝ} (hR : 0 ≤ R) (hDR : |D| ≤ R) :
    |Zonotope.coefficient R D| ≤ 1 := by -- --- PROOF ---
  rw [Zonotope.coefficient]
  split
  · simp
  · rw [abs_div, abs_of_nonneg hR, div_le_one (lt_of_le_of_ne hR (by tauto))]
    exact hDR

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
