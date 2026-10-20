module

public import CORALean.DiscrDynamics.GridPartition.Operations.Basic

@[expose] public section

/-!
# The members of `cellIntervals`

A box is listed by `cellIntervals` exactly when it is the box of a cell asked for and in range.

## Inputs
* `P` – grid partition
* `cs` – cell numbers
* `B` – box

## Hypotheses
* none

## Conclusion
* the box is listed iff it is the box of a requested cell
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- `B` is in `cellIntervals P cs` iff it is the box of an in-range cell of `cs`. -/
theorem GridPartition.mem_cellIntervals_iff (P : GridPartition n) (cs : List ℕ)
    (B : Real.Interval (Vec ℝ n)) :
    B ∈ P.cellIntervals cs ↔ ∃ c ∈ cs, 1 ≤ c ∧ c ≤ P.nrOfCells ∧ B = P.cellInterval c
      := by -- --- PROOF ---
  unfold GridPartition.cellIntervals
  simp only [List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨c, ⟨hc, h1, h2⟩, rfl⟩
    exact ⟨c, hc, h1, h2, rfl⟩
  · rintro ⟨c, hc, h1, h2, rfl⟩
    exact ⟨c, ⟨hc, h1, h2⟩, rfl⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
