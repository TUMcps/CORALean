module

public import CORALean.ContSet.Interval.Real.Operations.AbsMax
public import CORALean.ContSet.Interval.Real.Operations.Smul

@[expose] public section

/-!
# `Interval.absMax` of a non-negatively scaled box

The dominating matrix of `s • A` is `s` times `A`'s, at `s ≥ 0`: `smul` may
swap a pair of endpoints, and `absMax` takes the larger absolute value of the
pair whichever way round it comes.

## Inputs
* `A` – interval matrix
* `s` – scalar factor

## Hypotheses
* `hs` – scalar nonnegative

## Conclusion
* the largest absolute value of a scaled box is the scaled one
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {m n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.absMax_smul (A : Interval (Mat ℝ m n)) {s : ℝ} (hs : 0 ≤ s) : -- --- CONCL ---
    (Interval.smul s A).absMax = s • A.absMax := by -- --- PROOF ---
  funext i j
  simp only [Interval.absMax, Interval.smul, Entrywise.ofEntry, Entrywise.entry,
    Matrix.smul_apply, smul_eq_mul]
  rw [← mul_min_of_nonneg _ _ hs, ← mul_max_of_nonneg _ _ hs, abs_mul, abs_mul,
    abs_of_nonneg hs, ← mul_max_of_nonneg _ _ hs]
  rcases le_total (A.inf i j) (A.sup i j) with h | h
  · rw [min_eq_left h, max_eq_right h]
  · rw [min_eq_right h, max_eq_left h, max_comm]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
