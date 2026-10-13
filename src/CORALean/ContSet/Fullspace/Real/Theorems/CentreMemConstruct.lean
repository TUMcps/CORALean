module

public import CORALean.ContSet.Fullspace.Real.Operations.Centre

@[expose] public section

/-!
# The full space contains its centre

Trivially, as it contains everything.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Fullspace.centre_mem_construct (F : Fullspace n) : F.centre ∈ F.construct :=
  Set.mem_univ _

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
