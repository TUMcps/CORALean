import CORALean.ContSet.Interval.Real.Operations.Mask

/-!
# `Interval.tril`

CORA's `@interval/tril`: MATLAB's `tril(·, K)` on both bounds, which keeps the entries
on or below the `K`-th superdiagonal (`j ≤ i + K`) and
zeroes the rest. CORA requires `K ≥ 0` and defaults it to `0`, so `K : ℕ`.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {m n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Interval.tril (K : ℕ) (I : Interval (Mat ℝ m n)) : Interval (Mat ℝ m n) :=
  I.mask (fun i j => (j : ℕ) ≤ (i : ℕ) + K)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
