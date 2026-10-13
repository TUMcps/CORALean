module

public import CORALean.ContSet.Fullspace.Real.Operations.HPolytope
public import CORALean.ContSet.HPolytope.Real.Operations.ConstructFullspace

@[expose] public section

/-!
# `Fullspace.hPolytope` denotes the full space
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Fullspace.hPolytope_exact (F : Fullspace n) :
    F.hPolytope.construct = F.construct :=
  HPolytope.construct_fullspace

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
