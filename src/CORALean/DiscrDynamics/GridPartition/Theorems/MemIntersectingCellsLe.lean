module

public import CORALean.DiscrDynamics.GridPartition.Operations.IntersectingCells

@[expose] public section

/-!
# `intersectingCells` stays within the partition

Every number it returns is a cell or `0`: at most `nrOfCells`.

## Inputs
* `P` – grid partition
* `I` – box
* `c` – cell number

## Hypotheses
* `hc` – cell is returned

## Conclusion
* the cell number is within the cell count
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- Every number in `intersectingCells P I` is at most `nrOfCells`. -/
theorem GridPartition.mem_intersectingCells_le (P : GridPartition n)
    (I : Real.Interval (Vec ℝ n)) {c : ℕ} (hc : c ∈ P.intersectingCells I) :
    c ≤ P.nrOfCells := by
  unfold GridPartition.intersectingCells at hc
  split_ifs at hc <;>
    simp only [List.mem_append, List.mem_singleton, List.mem_filter, List.mem_range'_1] at hc <;>
    omega

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
