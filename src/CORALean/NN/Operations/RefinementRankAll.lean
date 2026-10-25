module

public import Mathlib.Data.Real.Basic

@[expose] public section

/-!
# Every neuron equally worth refining

The paper's simplest heuristic [1, Def. 4.7]: every neuron's rank is `1`. A bare constant, not a
function of a layer or a neuron index. `refineWorst`/`refineWorstNeurons` fed `fun _ =>
refinementRankAll` (or `fun _ _ => refinementRankAll`) then tie everywhere and fall to their own
earliest-index tie-break. Nothing here is proved and nothing here can be wrong: `encloseAt_outer`
holds at every schedule, so a constant rank is as sound a choice as `refinementRank`, only blind to
where the error actually is.

## Inputs
* none

## Output
* the constant rank one

## References

* [1] T. Ladner and M. Althoff. "Automatic Abstraction Refinement in Neural Network Verification
      using Sensitivity Analysis". Proceedings of the 26th ACM International Conference on Hybrid
      Systems: Computation and Control, 2023.
-/

-- Authors:       Claude Opus 5
-- Written:       11-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The rank under `σ`-All [1, Def. 4.7]: every neuron is equally worth
refining. -/
def refinementRankAll : ℝ := 1

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
