import CORALean.NN.Operations.ScheduleCons
import CORALean.NN.Operations.ScheduleHead

/-!
# The head of a pattern in front of a schedule is that pattern

Every index of the pattern is under the layer's width, so `cons`'s padding is never read.
-/

-- Authors:       Claude Opus 5.5
-- Written:       05-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Schedule.head_cons (t : OrderPattern n) (sch : Schedule) :
    Schedule.head (Schedule.cons t sch) n = t := by
  funext i
  -- every index of the pattern is under the width, so the padding is not reached
  exact dif_pos i.isLt

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
