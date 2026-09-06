import CORALean.ContSet.Interval.Real.Operations.Point
import CORALean.ContSet.Interval.Real.Operations.Center
import CORALean.ContSet.Interval.Real.Operations.Radius
import CORALean.ContSet.Interval.Real.Operations.IsNonempty
import CORALean.ContSet.Interval.Real.Operations.And
import CORALean.ContSet.Interval.Real.Operations.AndExact
import CORALean.ContSet.Interval.Real.Operations.Plus
import CORALean.ContSet.Interval.Real.Operations.Minus
import CORALean.ContSet.Interval.Real.Operations.LinComb
import CORALean.ContSet.Interval.Real.Operations.Mtimes
import CORALean.ContSet.Interval.Real.Operations.MulLo
import CORALean.ContSet.Interval.Real.Operations.MulHi
import CORALean.ContSet.Interval.Real.Operations.MtimesIntervalMat
import CORALean.ContSet.Interval.Real.Operations.MatMul
import CORALean.ContSet.Interval.Real.Operations.MatPow
import CORALean.ContSet.Interval.Real.Operations.Smul
import CORALean.ContSet.Interval.Real.Operations.OfBounds
import CORALean.ContSet.Interval.Real.Operations.SubsetOfBounds
import CORALean.ContSet.Interval.Real.Operations.Reindex

/-!
# What `Interval` computes

CORA's `plus`, `minus`, `linComb` and `mtimes` — the last at a plain matrix and
at an interval one — one file each, plus the constructor every other
representation's `interval` goes through: a box read off `2n` certified bounds.
`minus` is exact and unconditional, coordinatewise subtraction. `MatMul` is the
product of two interval matrices, not a `mtimes*` (its argument is a set of
matrices, not vectors), and `MatPow` is its plain recursive power — no lawful
`Pow` instance, since `matMul` is not associative up to equality. `Smul` scales
a box by a real, corner-swapped for a negative one.

`Point` and `Center`/`Radius` are the two readings of a box the enclosure
proofs elsewhere want: the degenerate one, and the centre-plus-deviation split.
`IsNonempty` is the predicate `Theorems/IsNonempty` characterises.
-/
