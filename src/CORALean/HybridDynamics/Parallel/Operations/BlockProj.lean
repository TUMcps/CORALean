module

public import CORALean.HybridDynamics.Parallel.Operations.Unstack

@[expose] public section

/-!
# `blockProj`

Block `c` of the product space as a linear map, `unstack` at `c`. It is the coordinate projection
a representation closed under preimages lifts a component's guard through (`HPolytope.comap`).
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {k : ℕ} {n : Fin k → ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def blockProj (c : Fin k) : Vec ℝ (∑ i, n i) →ₗ[ℝ] Vec ℝ (n c) where
  toFun z := unstack z c
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
