import CORALean.ContSet.Fullspace.Real.Operations.Centre

/-!
# The full space contains its centre

Trivially, as it contains everything.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Fullspace.centre_mem_construct (F : Fullspace n) : F.centre ∈ F.construct :=
  Set.mem_univ _

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
