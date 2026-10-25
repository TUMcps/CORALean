module

public import CORALean.DiscrDynamics.GridPartition.Theorems.MemCellIntervalsIff
public import CORALean.DiscrDynamics.GridPartition.Theorems.Basic
public import CORALean.ContSet.Conversion.Real.Theorems.IntervalZonotopeExact

@[expose] public section

/-!
# `cellZonotopes` are the cells

Each cell zonotope denotes exactly its cell box, as a nonempty box is exactly its zonotope.

## Inputs
* `P` – grid partition
* `cs` – cell numbers

## Hypotheses
* `hP` – partition well formed

## Conclusion
* each cell zonotope denotes its cell box
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The zonotopes of `cellZonotopes` denote the boxes of `cellIntervals`, one for one. -/
theorem GridPartition.cellZonotopes_exact (P : GridPartition n) (hP : P.IsWellFormed)
    (cs : List ℕ) : -- --- CONCL ---
    (P.cellZonotopes cs).map Real.Zonotope.construct =
      (P.cellIntervals cs).map Real.Interval.construct := by -- --- PROOF ---
  unfold GridPartition.cellZonotopes
  rw [List.map_map]
  apply List.map_congr_left
  intro B hB
  obtain ⟨c, _, h1, h2, rfl⟩ := (GridPartition.mem_cellIntervals_iff _ _ _).mp hB
  exact Real.Interval.zonotope_exact _ (GridPartition.cellInterval_nonempty P hP h1 h2)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
