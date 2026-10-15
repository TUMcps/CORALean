module

public import CORALean.DiscrDynamics.GridPartition.Operations.MeetingSubscripts

@[expose] public section

/-!
# `GridPartition.intersectingCells`

CORA's `@partition/intersectingCells(obj, I)` for a box `I` (the interval and numeric-point
branches; a zonotope or polytope goes through its interval hull, `intersectingCellsOf`),
default output `'indices'`: the numbers of the cells that possibly meet `I`, ascending, and a
trailing `0` if `I` leaves the state space. `0` alone if some dimension meets no segment. The second
output `error` and the `'subscripts'` option are not modelled.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `intersectingCells(P, I)`: the cells meeting `I`, within `tol`, and `0` if `I` sticks out. -/
noncomputable def GridPartition.intersectingCells (P : GridPartition n)
    (I : Real.Interval (Vec ℝ n)) : List ℕ :=
  if n = 0 ∨ ∃ j, P.meetingSubscripts I j = [] then [0]
  else
    -- the tensor product of the per-dimension subscripts, in cell order
    let MX := (List.range' 1 P.nrOfCells).filter fun c =>
      ∀ j, GridPartition.i2s P.nrOfSegments c j ∈ P.meetingSubscripts I j
    if ∃ j, I.inf j < P.dividers j 0 ∨ P.dividers j (P.nrOfSegments j) < I.sup j
    then MX ++ [0] else MX

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
