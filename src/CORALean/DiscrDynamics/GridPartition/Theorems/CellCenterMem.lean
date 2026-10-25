module

public import CORALean.DiscrDynamics.GridPartition.Operations.CellCenter
public import CORALean.DiscrDynamics.GridPartition.Theorems.Basic

@[expose] public section

/-!
# A cell's center is in the cell

In a well-formed partition `cellCenter` returns a point of each cell asked for.

## Inputs
* `P` – grid partition
* `cs` – cell numbers

## Hypotheses
* `hP` – partition well formed
* `hcs` – cell numbers in range

## Conclusion
* every returned center lies in one of the cells
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- Every point `cellCenter` returns lies in one of the cells asked for. -/
theorem GridPartition.cellCenter_mem (P : GridPartition n) (hP : P.IsWellFormed) {cs : List ℕ}
    (hcs : ∀ c ∈ cs, 0 < c ∧ c ≤ P.nrOfCells) : -- --- CONCL ---
    ∀ z ∈ P.cellCenter cs, ∃ c ∈ cs, z ∈ (P.cellInterval c).construct := by -- --- PROOF ---
  intro z hz
  unfold GridPartition.cellCenter at hz
  rw [if_pos hcs] at hz
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hz
  refine ⟨c, hc, ?_⟩
  rw [GridPartition.mem_interval_iff]
  intro j
  have := GridPartition.cellInterval_nonempty P hP (hcs c hc).1 (hcs c hc).2 j
  constructor <;> linarith

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
