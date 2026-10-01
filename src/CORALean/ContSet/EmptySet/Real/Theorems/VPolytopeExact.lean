import CORALean.ContSet.EmptySet.Real.Operations.VPolytope
import CORALean.ContSet.EmptySet.Real.Instances
import CORALean.ContSet.VPolytope.Real.Operations.ConstructEmptySet

/-!
# `EmptySet.vPolytope` denotes the empty set
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open ContSet

variable {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem EmptySet.vPolytope_exact (E : EmptySet n) :
    E.vPolytope.construct = construct E :=
  VPolytope.construct_emptySet

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
