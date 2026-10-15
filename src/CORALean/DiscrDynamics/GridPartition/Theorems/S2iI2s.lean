module

public import CORALean.DiscrDynamics.GridPartition.Theorems.I2sMem

@[expose] public section

/-!
# `s2i` undoes `i2s`

A cell number in `1 … N` is recovered from its subscripts.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- `s2i (i2s c) = c` for a cell `c` in `1 … N`: MATLAB's `ind2sub` followed by `sub2ind`. -/
theorem GridPartition.s2i_i2s (siz : Fin n → ℕ) {c : ℕ} (h1 : 1 ≤ c) (h2 : c ≤ ∏ j, siz j) :
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

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
