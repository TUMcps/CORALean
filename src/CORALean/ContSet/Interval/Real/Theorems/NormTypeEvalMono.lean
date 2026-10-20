module

public import CORALean.ContSet.Interval.Real.Operations.NormTypeEval

@[expose] public section

/-!
# Every supported norm is monotone in the absolute values of the entries

`1`, `Inf` and `'fro'` are built from `|M i j|` by sums, maxima and a square root, each of which
is monotone, so `|M| ≤ |N|` entrywise gives `‖M‖ ≤ ‖N‖`. Hence two matrices with the same absolute
values have the same norm, which is how the maximum over a box is attained at one corner.

## Inputs
* `p` – norm type
* `M` – first matrix
* `N` – second matrix

## Hypotheses
* `h` – absolute entries of `M` below those of `N`

## Conclusion
* the norm of `M` is at most the norm of `N`
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {m n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The norm of `type` is monotone in the entrywise absolute value. -/
theorem Interval.NormType.eval_mono (p : Interval.NormType) {M N : Mat ℝ m n}
    (h : ∀ i j, |M i j| ≤ |N i j|) : p.eval M ≤ p.eval N := by -- --- PROOF ---
  cases p with
  | one =>
    exact ciSup_mono (Set.finite_range _).bddAbove fun j =>
      Finset.sum_le_sum fun i _ => h i j
  | inf =>
    exact ciSup_mono (Set.finite_range _).bddAbove fun i =>
      Finset.sum_le_sum fun j _ => h i j
  | fro =>
    refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_)
    rw [← sq_abs (M i j), ← sq_abs (N i j)]
    exact pow_le_pow_left₀ (abs_nonneg _) (h i j) 2

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
