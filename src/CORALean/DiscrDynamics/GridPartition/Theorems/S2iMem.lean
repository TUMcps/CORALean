module

public import CORALean.DiscrDynamics.GridPartition.Operations.Basic

@[expose] public section

/-!
# `s2i` lands in `1 … N`

Subscripts in range give a cell number in range.

## Inputs
* `siz` – segments per dimension
* `sub` – subscripts

## Hypotheses
* `h` – subscripts in range

## Conclusion
* the cell number is within the cell count
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- Subscripts in range give a cell number in `1 … N`. -/
theorem GridPartition.s2i_mem (siz : Fin n → ℕ) {sub : Fin n → ℕ}
    (h : ∀ i, 0 < sub i ∧ sub i ≤ siz i) :
    1 ≤ GridPartition.s2i siz sub ∧ GridPartition.s2i siz sub ≤ ∏ j, siz j := by -- --- PROOF ---
  unfold GridPartition.s2i
  rw [if_pos h]
  let f : (i : Fin n) → Fin (siz i) := fun i => ⟨sub i - 1, by have := h i; omega⟩
  have key2 := (finPiFinEquiv f).isLt
  rw [finPiFinEquiv_apply] at key2
  have key3 : ∑ i, (sub i - 1) * GridPartition.multiplicator siz i < ∏ j, siz j := key2
  omega

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
