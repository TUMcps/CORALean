module

public import CORALean.DiscrDynamics.GridPartition.Operations.Basic

@[expose] public section

/-!
# The subscripts of a cell are in range

A cell `1 ≤ c ≤ N` has subscripts between `1` and `nrOfSegments`.

## Inputs
* `siz` – segments per dimension
* `c` – cell number
* `i` – dimension

## Hypotheses
* `h2` – cell number within the cell count
* `h1` – cell number at least one

## Conclusion
* the subscript lies between one and the segment count
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The subscripts `i2s` gives a cell in `1 … N` lie in `1 … siz i`. -/
theorem GridPartition.i2s_mem (siz : Fin n → ℕ) {c : ℕ} (h2 : c ≤ ∏ j, siz j) (h1 : 1 ≤ c)
    (i : Fin n) : 0 < GridPartition.i2s siz c i ∧ GridPartition.i2s siz c i ≤ siz i
      := by -- --- PROOF ---
  have hpos : 0 < siz i := by
    rcases Nat.eq_zero_or_pos (siz i) with h | h
    · -- a vanishing factor makes the product, hence `c`, vanish
      have : ∏ j, siz j = 0 := Finset.prod_eq_zero (Finset.mem_univ i) h
      omega
    · exact h
  have := Nat.mod_lt ((c - 1) / GridPartition.multiplicator siz i) hpos
  unfold GridPartition.i2s; omega

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
