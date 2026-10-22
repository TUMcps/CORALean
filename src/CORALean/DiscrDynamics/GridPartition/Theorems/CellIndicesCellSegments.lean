module

public import CORALean.DiscrDynamics.GridPartition.Theorems.I2sMem

@[expose] public section

/-!
# `cellIndices` undoes `cellSegments`

The cell numbers are recovered from their subscripts, for numbers in range.

## Inputs
* `P` – grid partition
* `cs` – cell numbers

## Hypotheses
* `h` – cell numbers in range

## Conclusion
* the subscripts map back to the cell numbers
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `s2i (i2s c) = c` for a cell `c` in `1 … N`: MATLAB's `ind2sub` followed by `sub2ind`. -/
theorem GridPartition.aux_s2i_i2s (siz : Fin n → ℕ) {c : ℕ} (h1 : 1 ≤ c)
    (h2 : c ≤ ∏ j, siz j) : -- --- CONCL ---
    GridPartition.s2i siz (GridPartition.i2s siz c) = c := by -- --- PROOF ---
  have hin := GridPartition.i2s_mem siz h2 h1
  unfold GridPartition.s2i
  rw [if_pos hin]
  -- Mathlib's mixed-radix equivalence has the same digits
  let a : Fin (∏ j, siz j) := ⟨c - 1, by omega⟩
  have key2 := congrArg Fin.val ((finPiFinEquiv (n := siz)).apply_symm_apply a)
  rw [finPiFinEquiv_apply] at key2
  have : ∀ i, (GridPartition.i2s siz c i - 1) = ((finPiFinEquiv (n := siz)).symm a i).val := by
    intro i; unfold GridPartition.i2s; rfl
  simp only [this]
  have h3 : ∑ i, ((finPiFinEquiv (n := siz)).symm a i).val * GridPartition.multiplicator siz i =
      c - 1 := key2
  omega


-- =======================================  MAIN THEOREM  ======================================= --

/-- `cellIndices (cellSegments cs) = cs` for cell numbers in `1 … N`. -/
theorem GridPartition.cellIndices_cellSegments (P : GridPartition n) {cs : List ℕ}
    (h : ∀ c ∈ cs, 1 ≤ c ∧ c ≤ P.nrOfCells) :
    P.cellIndices (P.cellSegments cs) = cs := by
  unfold GridPartition.cellIndices GridPartition.cellSegments
  rw [List.map_map]
  conv_rhs => rw [← List.map_id cs]
  exact List.map_congr_left fun c hc => GridPartition.aux_s2i_i2s _ (h c hc).1 (h c hc).2

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
