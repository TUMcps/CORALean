module

public import CORALean.DiscrDynamics.GridPartition.Operations.Basic
public import CORALean.ContSet.Conversion.Real.Theorems.IntervalHPolytopeExact

@[expose] public section

/-!
# `cellPolytopes` are the cells

Each cell polytope denotes exactly its cell box.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The polytopes of `cellPolytopes` denote the boxes of `cellIntervals`, one for one. -/
theorem GridPartition.cellPolytopes_exact (P : GridPartition n) (cs : List ℕ) :
    (P.cellPolytopes cs).map Real.HPolytope.construct =
      (P.cellIntervals cs).map Real.Interval.construct := by
  unfold GridPartition.cellPolytopes
  rw [List.map_map]
  exact List.map_congr_left fun B _ => Real.Interval.hPolytope_exact B

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
