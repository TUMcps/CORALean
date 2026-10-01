import CORALean.HybridDynamics.Parallel.Operations.BlockProj

/-!
# `blockProj` reads a block

`blockProj c` applied to a point is its block `c`, by definition.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {k : ℕ} {n : Fin k → ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

@[simp] theorem blockProj_apply (c : Fin k) (z : Vec ℝ (∑ i, n i)) :
    blockProj c z = unstack z c := rfl

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
