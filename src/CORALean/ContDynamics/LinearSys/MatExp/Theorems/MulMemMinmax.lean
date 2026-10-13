import CORALean.ContSet.Interval.Real.Interval
/-!
# Scaling an interval-bounded value keeps it interval-bounded

`corrTerm` and `constCorrTerm` place a coefficient between a bound `L` and
zero and then scale it by a sign-varying factor; this is the one fact that
survives either sign, so both correction matrices reduce their containment
proof to it rather than casing on the sign twice.
-/

-- Authors:       Claude Opus 5
-- Written:       18-August-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- A value between `L` and `0`, scaled by anything, stays between `L * w` and `0`
on whichever side the sign puts it. -/
theorem mul_mem_minmax {L u w : ℝ} (hLu : L ≤ u) (hu0 : u ≤ 0) :
    min (L * w) 0 ≤ u * w ∧ u * w ≤ max (L * w) 0 := by
  rcases le_total 0 w with hw | hw
  · exact ⟨le_trans (min_le_left _ _) (by nlinarith), le_trans (by nlinarith) (le_max_right _ _)⟩
  · exact ⟨le_trans (min_le_right _ _) (by nlinarith), le_trans (by nlinarith) (le_max_left _ _)⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
