module

public import CORALean.ContSet.Interval.Real.Operations.Basic
public import CORALean.Global.Cost

@[expose] public section

/-!
# `Interval.mtimesCost`

Asserted, not proved: `Operations/Mtimes.lean` forms, per output row and per
summand, the two products `M i k * inf k` and `M i k * sup k` and takes their
`min` and their `max`, then folds each of the two sums — `2 * n` products,
`2 * n` comparisons and `2 * (n - 1)` additions per row, bounded by `6 * n`, and two writes per row.

Not `Cost.matVec`, which is one product and one sum per row: an interval
matrix-vector product does the work of two and compares as well.
-/

-- Authors:       Claude Opus 5, Claude Sonnet 5.5
-- Written:       07-September-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `Interval.mtimes` costs at `M : Mat ℝ m n`: at most `6 * n` scalar operations per output
row, and `2 * m` writes for the two bounds of every row. -/
def Interval.mtimesCost (m n : ℕ) : Cost := ⟨6 * (m * n) + 2 * m⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
