module

public import CORALean.NN.Definitions.Schedule

@[expose] public section

/-!
# A schedule's tail

What the rest of a network reads, the head layer's pattern dropped.
-/

-- Authors:       Claude Opus 5.5
-- Written:       05-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What the rest of a network reads, the head layer's pattern dropped. -/
def Schedule.tail (sch : Schedule) : Schedule := fun l => sch (l + 1)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
