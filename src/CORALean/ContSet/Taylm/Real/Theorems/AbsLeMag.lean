import CORALean.ContSet.Taylm.Real.Operations.Mag
import Mathlib.Tactic.Linarith

/-!
# The hull of a Taylor model lies within its magnitude
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.abs_le_mag (T : Taylm n) {ξ : ℝ}
    (hξ : ξ ∈ Set.Icc (min T.constCoef T.bounds.1) (max T.constCoef T.bounds.2)) :
    |ξ| ≤ T.mag := by -- --- PROOF ---
  unfold Taylm.mag
  have h1 := le_max_left |T.constCoef| (max |T.bounds.1| |T.bounds.2|)
  have h2 := le_max_left |T.bounds.1| |T.bounds.2|
  have h3 := le_max_right |T.bounds.1| |T.bounds.2|
  have h4 := le_max_right |T.constCoef| (max |T.bounds.1| |T.bounds.2|)
  rw [abs_le]
  constructor
  · -- the lower end of the hull is the centre or the range's bottom
    have := hξ.1
    rcases min_choice T.constCoef T.bounds.1 with h | h <;> rw [h] at this
    · linarith [neg_abs_le T.constCoef]
    · linarith [neg_abs_le T.bounds.1]
  · have := hξ.2
    rcases max_choice T.constCoef T.bounds.2 with h | h <;> rw [h] at this
    · linarith [le_abs_self T.constCoef]
    · linarith [le_abs_self T.bounds.2]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
