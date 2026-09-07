import CORALean.NN.Operations.Refine

/-!
# The refinement loop's schedule

`k` steps, each at the `(layer, neuron)` pair `pick` names from the schedule
reached so far. Nothing constrains `pick`, and `Theorems.EncloseAtOuter` is
why nothing has to: soundness holds at every schedule `refine` can reach.
-/

-- Authors:       Tobias Ladner
-- Written:       05-September-2026
-- Last update:   06-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The loop itself: `k` steps, each at the `(layer, neuron)` pair `pick` names
from the schedule reached so far. -/
def Schedule.refineLoop (pick : Schedule → ℕ × ℕ) (sch : Schedule) : ℕ → Schedule
  | 0 => sch
  | k + 1 => Schedule.refineLoop pick (Schedule.refine sch (pick sch).1 (pick sch).2) k

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
