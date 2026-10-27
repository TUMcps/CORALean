module

public import CORALean.NN.Operations.Refine

@[expose] public section

/-!
# The refinement loop's schedule

The loop is [1, Alg. 3].

`k` steps, each at the `(layer, neuron)` pair `pick` names from the schedule
reached so far. Nothing constrains `pick`, and `Theorems.EncloseAtOuter` is
why nothing has to: soundness holds at every schedule `refine` can reach.

## Inputs
* `pick` – layer and neuron to refine next
* `sch` – initial schedule

## Output
* schedule after the given number of refinement steps

## References

* [1] [T. Ladner and M. Althoff. "Automatic Abstraction Refinement in Neural Network Verification
      using Sensitivity Analysis". Proceedings of the 26th ACM International Conference on Hybrid
      Systems: Computation and Control,
      2023.](../../../../references/2023/ladner-hscc-abstraction-refinement.md)
-/

-- Authors:       Claude Opus 5
-- Written:       05-September-2026
-- Last update:   06-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The loop itself: `k` steps, each at the `(layer, neuron)` pair `pick` names
from the schedule reached so far. -/
def Schedule.refineLoop (pick : Schedule → ℕ × ℕ) (sch : Schedule) : ℕ → Schedule
  | 0 => sch
  | k + 1 => Schedule.refineLoop pick (Schedule.refine sch (pick sch).1 (pick sch).2) k

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
