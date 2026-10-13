import CORALean.ContSet.Interval.Real.Operations.Mask

/-!
# `Interval.triu`

CORA's `@interval/triu`: MATLAB's `triu(·, K)` on both bounds, which keeps the entries
on or above the `K`-th superdiagonal (`i + K ≤ j`) and
zeroes the rest. CORA requires `K ≥ 0` and defaults it to `0`, so `K : ℕ`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {m n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Interval.triu (K : ℕ) (I : Interval (Mat ℝ m n)) : Interval (Mat ℝ m n) :=
  I.mask (fun i j => (i : ℕ) + K ≤ (j : ℕ))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
