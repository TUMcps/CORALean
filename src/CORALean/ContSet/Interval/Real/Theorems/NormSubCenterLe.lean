import CORALean.ContSet.Interval.Real.Operations.Radius2
import CORALean.ContSet.Interval.Real.Instances
import CORALean.ContSet.Interval.Real.Theorems.AbsSubCenterLe

/-!
# Every member of a box is within `Interval.radius₂` of the centre

In `‖·‖₂`: coordinatewise a member's distance to the centre is at most the half-width
(`abs_sub_center_le`), and the Euclidean norm is monotone in magnitudes.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open ContSet

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.norm₂_sub_center_le {I : Interval (Vec ℝ n)} {x : Vec ℝ n}
    (hx : x ∈ construct I) : ‖x - I.center‖₂ ≤ I.radius₂ := by -- --- PROOF ---
  unfold Interval.radius₂ norm₂
  refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ => ?_)
  have h := Interval.abs_sub_center_le hx i
  rw [Pi.sub_apply, ← sq_abs, ← sq_abs (I.radius i)]
  exact pow_le_pow_left₀ (abs_nonneg _) (le_trans h (le_abs_self _)) 2

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
