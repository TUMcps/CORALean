import CORALean.ContSet.Interval.Real.Operations.Mtimes

/-!
# `Interval.mtimes`'s width, row by row

An equality, not a bound, and unconditional: it holds whether or not `I` is
itself a nonempty interval, the absolute value on the right absorbing the
`I.sup k < I.inf k` case the same way it absorbs a negative `M i k`.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.mtimes_width (M : Mat ℝ m n) (I : Interval (Vec ℝ n)) (i : Fin m) :
    (Interval.mtimes M I).sup i - (Interval.mtimes M I).inf i
      = ∑ k, |M i k| * |I.sup k - I.inf k| := by -- --- PROOF ---
  show (∑ k, max (M i k * I.inf k) (M i k * I.sup k))
      - ∑ k, min (M i k * I.inf k) (M i k * I.sup k)
      = ∑ k, |M i k| * |I.sup k - I.inf k|
  rw [← Finset.sum_sub_distrib]
  -- each summand is `max - min` of the two endpoint products, an absolute difference
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [max_sub_min_eq_abs, ← mul_sub, abs_mul]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
