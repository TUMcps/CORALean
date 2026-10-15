module

public import CORALean.DiscrDynamics.GridPartition.Operations.Basic

@[expose] public section

/-!
# `GridPartition.meetingSubscripts`

The `currentIndex{iDim}` of CORA's `intersectingCells`: the segments of dimension `j` whose
closed range meets `[inf - tol, sup + tol]`, from `find(E(2:end) & F(1:(end-1)))`.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The subscripts `k` of dimension `j` with `d(k) ≥ inf - tol` and `d(k - 1) ≤ sup + tol`. -/
noncomputable def GridPartition.meetingSubscripts (P : GridPartition n)
    (I : Real.Interval (Vec ℝ n)) (j : Fin n) : List ℕ :=
  (List.range' 1 (P.nrOfSegments j)).filter fun k =>
    I.inf j - GridPartition.tol ≤ P.dividers j k ∧
      P.dividers j (k - 1) ≤ I.sup j + GridPartition.tol

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
