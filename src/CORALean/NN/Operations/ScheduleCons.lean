import CORALean.NN.Definitions.Schedule

/-!
# A pattern in front of a schedule

How the induction over a network builds a schedule, one layer's pattern at a time.
-/

-- Authors:       Claude Opus 5.5
-- Written:       05-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- A pattern in front of a schedule, which is how the induction builds one. The
indices past the layer's width are never read, so `0` will do for them. -/
def Schedule.cons (t : OrderPattern n) (sch : Schedule) : Schedule
  | 0 => fun j => if h : j < n then t ⟨j, h⟩ else 0
  | l + 1 => sch l

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
