module

public import CORALean.DiscrDynamics.GridPartition.Operations.OfInterval

@[expose] public section

/-!
# `partition(I, segs)` covers `I`

The state space of the evenly cut partition is the box it was cut from.

## Inputs
* `I` – box
* `segs` – segments per dimension

## Hypotheses
* `h` – every segment count positive

## Conclusion
* the partition covers the box
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- `partition(I, segs).intervals = I` when every dimension has a segment. -/
theorem GridPartition.ofInterval_intervals (I : Real.Interval (Vec ℝ n)) {segs : Fin n → ℕ}
    (h : ∀ j, 0 < segs j) : (GridPartition.ofInterval I segs).intervals = I := by
  have : ∀ j, ¬ (0 = segs j) := fun j => (h j).ne
  cases I
  simp [GridPartition.intervals, GridPartition.ofInterval, this]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
