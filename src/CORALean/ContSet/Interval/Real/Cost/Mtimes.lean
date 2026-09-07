import CORALean.ContSet.Interval.Real.Operations.Mtimes
import CORALean.Global.Cost

/-!
# `Interval.mtimesCost`

Asserted, not proved: `Operations/Mtimes.lean` forms, per output row and per
summand, the two products `M i k * inf k` and `M i k * sup k` and takes their
`min` and their `max`, then folds each of the two sums — `2 * n` products,
`2 * n` comparisons and `2 * (n - 1)` additions per row, bounded by `6 * n`.

Not `Cost.matVec`, which is one product and one sum per row: an interval
matrix-vector product does the work of two and compares as well.
-/

-- Authors:       Tobias Ladner
-- Written:       07-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `Interval.mtimes` costs at `M : Mat ℝ m n`: at most `6 * n` scalar
operations per output row. -/
def Interval.mtimesCost (m n : ℕ) : Cost := ⟨6 * (m * n)⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
