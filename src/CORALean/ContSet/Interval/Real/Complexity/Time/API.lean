import CORALean.ContSet.Interval.Real.Complexity.Time.Plus
import CORALean.ContSet.Interval.Real.Complexity.Time.LinComb
import CORALean.ContSet.Interval.Real.Complexity.Time.Mtimes
import CORALean.ContSet.Interval.Real.Complexity.Time.Intersection

/-!
# What running `Interval`'s operations costs

Scalar-operation counts against `Global/Cost.lean`'s model, one `def` per
operation, every one of them **asserted** — read off the operation's definition
by hand, never `rfl` against it.

This is the directory `Interval` has something to say in and `Complexity/Space/` does
not: a box carries no runtime-computed size to state a theorem about, but it
very much costs something to compute, and the count is what says how much.
`reduce` is not among them, a box being at order one already.

Every count is a fixed polynomial in the ambient dimensions, since no operand
size can vary: `plus`, `linComb` and `intersection` are `2 * n`, `mtimes` at
most `6 * m * n`, which is where a box beats a zonotope and why
`LinearSysDT.reach` over boxes would pay no reduction at all.
-/
