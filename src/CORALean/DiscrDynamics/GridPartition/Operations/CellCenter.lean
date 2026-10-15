module

public import CORALean.DiscrDynamics.GridPartition.Operations.Basic

@[expose] public section

/-!
# `GridPartition.cellCenter`

CORA's `@partition/cellCenter(Obj, cellNrs)`: the midpoint of each cell given, or `[]` if one is
out of range. The one-argument call reads the property `actualSegmentNr`, which the class no
longer has, and fails; it is not modelled.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `cellCenter(P, cellNrs)`: the centre of each cell, `(left + right) / 2` per dimension. -/
noncomputable def GridPartition.cellCenter (P : GridPartition n) (cellNrs : List ℕ) :
    List (Vec ℝ n) :=
  if ∀ c ∈ cellNrs, 0 < c ∧ c ≤ P.nrOfCells then
    cellNrs.map fun c j => ((P.cellInterval c).inf j + (P.cellInterval c).sup j) / 2
  else []

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
