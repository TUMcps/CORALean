module

public import CORALean.DiscrDynamics.GridPartition.Theorems.ExactIntersectingCellsExact

@[expose] public section

/-!
# The shares of `exactIntersectingCells` add up to one

The outside share is `1 - Σ` of the others, so the whole `iProp`, padded with zeros where CORA
returns the single entry `1`, sums to `1`. The sum over cells being at most `1` is not shown.

## Inputs
* `P` – grid partition
* `X` – set

## Hypotheses
* none

## Conclusion
* the shares add up to one
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet

variable {n : ℕ} {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [Real.IntervalOuter S]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The entries of a list of length `N` sum to its sum. -/
theorem GridPartition.aux_sum_getD_eq (l : List ℝ) {N : ℕ} (h : l.length = N) :
    ∑ i : Fin N, l.getD i 0 = l.sum := by
  subst h
  rw [← Fin.sum_univ_getElem]
  exact Finset.sum_congr rfl fun i _ => by simp [List.getD_eq_getElem?_getD]


-- =======================================  MAIN THEOREM  ======================================= --

/-- The `nrOfCells + 1` entries of `iProp` sum to `1`. -/
theorem GridPartition.exactIntersectingCells_sum (P : GridPartition n) (X : S n) :
    ∑ s : Fin (P.nrOfCells + 1), (P.exactIntersectingCells X).iProp.getD s 0 = 1
      := by -- --- PROOF ---
  unfold GridPartition.exactIntersectingCells
  split_ifs with h
  · dsimp only
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, List.getD_cons_zero, Fin.val_succ, List.getD_cons_succ]
    rw [GridPartition.aux_sum_getD_eq _ (by simp)]
    simp
  · dsimp only
    rw [Fin.sum_univ_succ]
    simp

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
