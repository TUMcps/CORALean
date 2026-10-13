import CORALean.ContSet.Fullspace.Real.Operations.EnclosePoints

/-!
# `Fullspace.enclosePoints` encloses the points
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Fullspace.range_subset_enclosePoints {p : ℕ} (pts : Fin p → Vec ℝ n) :
    Set.range pts ⊆ (Fullspace.enclosePoints pts).construct :=
  fun _ _ => Set.mem_univ _

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
