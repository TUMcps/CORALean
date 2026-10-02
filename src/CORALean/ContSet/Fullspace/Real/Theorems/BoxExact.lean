import CORALean.ContSet.Fullspace.Real.Operations.Box

/-!
# `Fullspace.box` is exact

The box of the full space denotes the full space.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Fullspace.box_exact (F : Fullspace n) : F.box.construct = F.construct := rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
