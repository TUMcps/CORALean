import CORALean.ContSet.PolyZonotope.Real.Operations.SplitGen

/-!
# `PolyZonotope.splitMany`

The pieces `containsPointSet` works with: `k` rounds, every piece replaced by the two halves
`splitGen` gives.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def PolyZonotope.splitMany (pZ : PolyZonotope (Vec ℝ n)) :
    ℕ → List (PolyZonotope (Vec ℝ n))
  | 0 => [pZ]
  | k + 1 => (pZ.splitMany k).flatMap fun q => [q.splitGen.1, q.splitGen.2]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
