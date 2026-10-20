module

public import CORALean.DiscrDynamics.GridPartition.Operations.OfInterval
public import CORALean.DiscrDynamics.GridPartition.Theorems.I2sMem

@[expose] public section

/-!
# The cells of `partition(I, segs)` have equal width

In each dimension every cell is `(sup - inf) / segs` wide: the grid is uniform.

## Inputs
* `I` – box
* `segs` – segments per dimension
* `c` – cell number
* `j` – dimension

## Hypotheses
* `h` – every segment count positive
* `h1` – cell number at least one
* `h2` – cell number within the cell count

## Conclusion
* the cell width is the box width over the segment count
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- Every cell of `partition(I, segs)` is `(sup - inf) / segs j` wide in dimension `j`. -/
theorem GridPartition.ofInterval_cell_width (I : Real.Interval (Vec ℝ n)) {segs : Fin n → ℕ}
    (h : ∀ j, 0 < segs j) {c : ℕ} (h1 : 1 ≤ c)
    (h2 : c ≤ (GridPartition.ofInterval I segs).nrOfCells) (j : Fin n) : -- --- CONCL ---
    ((GridPartition.ofInterval I segs).cellInterval c).sup j -
        ((GridPartition.ofInterval I segs).cellInterval c).inf j =
      (I.sup j - I.inf j) / segs j := by -- --- PROOF ---
  have hs := GridPartition.i2s_mem (GridPartition.ofInterval I segs).nrOfSegments h2 h1 j
  have hm : (0 : ℝ) < segs j := by exact_mod_cast h j
  simp only [GridPartition.cellInterval, GridPartition.ofInterval] at hs ⊢
  generalize GridPartition.i2s segs c j = s at hs ⊢
  obtain ⟨hs1, hs2⟩ := hs
  have hcast : ((s - 1 : ℕ) : ℝ) = (s : ℝ) - 1 := by
    rw [Nat.cast_sub hs1]; simp
  have hne : ¬ (s - 1 = segs j) := by omega
  by_cases hsm : s = segs j
  · -- the last segment ends on `sup` itself
    rw [if_pos hsm, if_neg hne, hcast, hsm]
    field_simp
    ring
  · rw [if_neg hsm, if_neg hne, hcast]
    ring

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
