module

public import CORALean.DiscrDynamics.GridPartition.Theorems.S2iI2s

@[expose] public section

/-!
# `cellIndices` undoes `cellSegments`

The cell numbers are recovered from their subscripts, for numbers in range.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- `cellIndices (cellSegments cs) = cs` for cell numbers in `1 … N`. -/
theorem GridPartition.cellIndices_cellSegments (P : GridPartition n) {cs : List ℕ}
    (h : ∀ c ∈ cs, 1 ≤ c ∧ c ≤ P.nrOfCells) :
    P.cellIndices (P.cellSegments cs) = cs := by
  unfold GridPartition.cellIndices GridPartition.cellSegments
  rw [List.map_map]
  conv_rhs => rw [← List.map_id cs]
  exact List.map_congr_left fun c hc => GridPartition.s2i_i2s _ (h c hc).1 (h c hc).2

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
