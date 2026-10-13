import CORALean.ContSet.Interval.Real.Operations.Origin
import CORALean.ContSet.Interval.Real.Theorems.MemPoint

/-!
# `Interval.origin` is exactly the origin

Both bounds are `0`, so the only point is the origin.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Entrywise


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.origin_exact (n : ℕ) : (Interval.origin n).construct = {0} := by -- --- PROOF ---
  ext x
  constructor
  · intro hx
    refine funext fun i => le_antisymm ?_ ?_
    · exact (hx i).2
    · exact (hx i).1
  · rintro rfl
    exact Interval.mem_point _

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
