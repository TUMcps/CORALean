import CORALean.NN.Definitions.Schedule

/-!
# A schedule's head layer

The head layer's own pattern, cut to the width that layer has: a layer reads its width here.
-/

-- Authors:       Tobias Ladner
-- Written:       05-September-2026
-- Last update:   23-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The head layer's own pattern, cut to the width that layer has. -/
def Schedule.head (sch : Schedule) (n : ℕ) : OrderPattern n := fun i => sch 0 i.val

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
