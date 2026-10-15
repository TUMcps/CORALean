module

public import CORALean.DiscrDynamics.GridPartition.Operations.Basic

@[expose] public section

/-!
# `partition(dividers)` covers the first to the last divider

The state space of a partition built from dividers runs from the head to the last of each list.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The state space of `partition(dividers)` has the first and last divider as its bounds. -/
theorem GridPartition.ofDividers_intervals (v : Fin n → List ℝ) (h : ∀ j, v j ≠ [])
    (j : Fin n) : (GridPartition.ofDividers v).intervals.inf j = (v j).head (h j) ∧
      (GridPartition.ofDividers v).intervals.sup j = (v j).getLast (h j) := by -- --- PROOF ---
  obtain ⟨a, l, hl⟩ := List.exists_cons_of_ne_nil (h j)
  simp only [GridPartition.intervals, GridPartition.ofDividers]
  constructor
  · simp [hl]
  · rw [List.getLast_eq_getElem]
    have hlen : (v j).length - 1 < (v j).length := by
      have := List.length_pos_iff.mpr (h j); omega
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlen, Option.getD_some]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
