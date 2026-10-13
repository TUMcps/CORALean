import CORALean.HybridDynamics.Parallel.Operations.BlockProj

/-!
# `blockProj` reads a block

`blockProj c` applied to a point is its block `c`, by definition.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {k : ℕ} {n : Fin k → ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

@[simp] theorem blockProj_apply (c : Fin k) (z : Vec ℝ (∑ i, n i)) :
    blockProj c z = unstack z c := rfl

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
