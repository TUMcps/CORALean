module

public import CORALean.ContSet.Interval.Real.Operations.AbsMax
public import CORALean.ContSet.Interval.Real.Theorems.MemMat

@[expose] public section

/-!
# `Interval.absMax` is CORA's `abs` of an interval matrix

`abs(intMat)` is `supremum(abs(intMat.int))`: the entrywise supremum of `|M i j|`. On a nonempty
box that is `max |inf| |sup|` (`absMax`), and the corner of larger magnitude attains it, so it is
the greatest value, not only an upper bound. The corners are chosen per entry, which is allowed
because the box is a product of its entries.

## Inputs
* `A` – interval matrix
* `i` – row index
* `j` – column index

## Hypotheses
* `hA` – `A` has ordered bounds

## Conclusion
* the largest absolute value is the greatest absolute entry over the box
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {m n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- `absMax` is the entrywise supremum of the absolute values of the members, and is attained. -/
theorem Interval.absMax_isGreatest (A : Interval (Mat ℝ m n)) (hA : ∀ p q, A.inf p q ≤ A.sup p q)
    (i : Fin m) (j : Fin n) : -- --- CONCL ---
    IsGreatest ((fun M : Mat ℝ m n => |M i j|) '' A.construct) (A.absMax i j) := by -- --- PROOF ---
  classical
  refine ⟨?_, ?_⟩
  · -- the corner of larger magnitude in every entry
    refine ⟨Matrix.of fun p q => if |A.inf p q| ≤ |A.sup p q| then A.sup p q else A.inf p q,
      Interval.mem_mat_iff.mpr fun p q => ?_, ?_⟩
    · simp only [Matrix.of_apply]
      split_ifs
      · exact ⟨hA p q, le_rfl⟩
      · exact ⟨le_rfl, hA p q⟩
    · simp only [Matrix.of_apply, Interval.absMax]
      split_ifs with h
      · rw [max_eq_right h]
      · rw [max_eq_left (not_le.mp h).le]
  · rintro _ ⟨M, hM, rfl⟩
    have h := Interval.mem_mat_iff.mp hM i j
    show |M i j| ≤ max |A.inf i j| |A.sup i j|
    rw [abs_le]
    exact ⟨by linarith [neg_abs_le (A.inf i j), le_max_left |A.inf i j| |A.sup i j|, h.1],
      h.2.trans ((le_abs_self _).trans (le_max_right _ _))⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
