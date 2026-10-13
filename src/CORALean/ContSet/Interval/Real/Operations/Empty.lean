import CORALean.ContSet.Interval.Real.Interval

/-!
# `Interval.empty`

CORA's `interval.empty(n)`, which is an `n × 0` interval. The model here has no zero-width
interval, so the empty box is a crossed one: lower bound `1`, upper bound `0`, in every
coordinate.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Interval.empty (n : ℕ) : Interval (Vec ℝ n) := ⟨fun _ => 1, fun _ => 0⟩


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
