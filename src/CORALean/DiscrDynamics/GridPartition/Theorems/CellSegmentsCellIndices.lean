module

public import CORALean.DiscrDynamics.GridPartition.Theorems.I2sS2i

@[expose] public section

/-!
# `cellSegments` undoes `cellIndices`

The subscripts are recovered from their cell numbers, for subscripts in range.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- `cellSegments (cellIndices vs) = vs` for subscript vectors in range. -/
theorem GridPartition.cellSegments_cellIndices (P : GridPartition n) {vs : List (Fin n → ℕ)}
    (h : ∀ v ∈ vs, ∀ i, 0 < v i ∧ v i ≤ P.nrOfSegments i) :
    P.cellSegments (P.cellIndices vs) = vs := by
  unfold GridPartition.cellIndices GridPartition.cellSegments
  rw [List.map_map]
  conv_rhs => rw [← List.map_id vs]
  exact List.map_congr_left fun v hv => GridPartition.i2s_s2i _ (h v hv)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
