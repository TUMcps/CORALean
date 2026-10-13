import CORALean.ContSet.EmptySet.Real.Operations.HPolytope
import CORALean.ContSet.EmptySet.Real.Instances
import CORALean.ContSet.HPolytope.Real.Operations.ConstructEmptySet

/-!
# `EmptySet.hPolytope` denotes the empty set
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open ContSet

variable {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem EmptySet.hPolytope_exact (E : EmptySet n) :
    E.hPolytope.construct = construct E :=
  HPolytope.construct_emptySet

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
