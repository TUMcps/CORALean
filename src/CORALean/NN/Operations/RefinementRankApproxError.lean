module

public import CORALean.Global.Tensor
public import Mathlib.Data.Real.Basic

@[expose] public section

/-!
# A neuron's own approximation error

The paper's heuristic [1, Def. 4.9]: neuron `j`'s rank is its own
approximation error and nothing else — no weighing by how much that error
moves the output, which is what `refinementRank` [1, Def. 4.12] adds on top.

Nothing here is proved and nothing here can be wrong: `encloseAt_outer`
holds at every schedule, so this only decides where the next order is
spent, same as `refinementRank`.

## References

* [1] T. Ladner and M. Althoff. "Automatic Abstraction Refinement in Neural
      Network Verification using Sensitivity Analysis". HSCC 2023.
-/

-- Authors:       Claude Opus 5
-- Written:       11-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Neuron `j`'s rank under `σ`-Approximation-Error [1, Def. 4.9]: the
error its own relaxation leaves, and nothing else. -/
def refinementRankApproxError (d : Vec ℝ n) (j : Fin n) : ℝ := |d j|

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
