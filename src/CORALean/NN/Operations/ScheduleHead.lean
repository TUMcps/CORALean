module

public import CORALean.NN.Definitions.Schedule

@[expose] public section

/-!
# A schedule's head layer

The head layer's own pattern, cut to the width that layer has: a layer reads its width here.
-/

-- Authors:       Claude Opus 5.5
-- Written:       05-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The head layer's own pattern, cut to the width that layer has. -/
def Schedule.head (sch : Schedule) (n : ℕ) : OrderPattern n := fun i => sch 0 i.val

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
