module

public import CORALean.DiscrDynamics.GridPartition.Theorems.I2sMem
public import CORALean.DiscrDynamics.GridPartition.Theorems.Basic

@[expose] public section

/-!
# A cell lies in the state space

In a well-formed partition each cell box is inside the box the partition covers.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- Every cell of a well-formed partition is inside its state space. -/
theorem GridPartition.cell_subset_intervals (P : GridPartition n) (hP : P.WellFormed) {c : ℕ}
    (h1 : 1 ≤ c) (h2 : c ≤ P.nrOfCells) :
    (P.cellInterval c).construct ⊆ P.intervals.construct := by -- --- PROOF ---
  intro x hx
  rw [GridPartition.mem_interval_iff] at hx ⊢
  intro j
  have hs := GridPartition.i2s_mem P.nrOfSegments h2 h1 j
  have hc := hx j
  simp only [GridPartition.cellInterval] at hc
  simp only [GridPartition.intervals]
  have a := (hP j).2 0 (GridPartition.i2s P.nrOfSegments c j - 1) (by omega) (by omega)
  have b := (hP j).2 (GridPartition.i2s P.nrOfSegments c j) (P.nrOfSegments j) hs.2 le_rfl
  constructor <;> linarith [hc.1, hc.2]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
