module

public import CORALean.ContSet.EmptySet.Real.Operations.VPolytope
public import CORALean.ContSet.EmptySet.Real.Instances
public import CORALean.ContSet.VPolytope.Real.Operations.ConstructEmptySet

@[expose] public section

/-!
# `EmptySet.vPolytope` denotes the empty set
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

theorem EmptySet.vPolytope_exact (E : EmptySet n) :
    E.vPolytope.construct = construct E :=
  VPolytope.construct_emptySet

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
