import CORALean.ContSet.Interval.Real.Operations.Point
import CORALean.ContSet.Interval.Real.Operations.CenterRadius
import CORALean.ContSet.Interval.Real.Operations.And
import CORALean.ContSet.Interval.Real.Operations.Plus
import CORALean.ContSet.Interval.Real.Operations.LinComb
import CORALean.ContSet.Interval.Real.Operations.Mtimes
import CORALean.ContSet.Interval.Real.Operations.MtimesIntervalMat
import CORALean.ContSet.Interval.Real.Operations.OfBounds
import CORALean.ContSet.Interval.Real.Operations.Reindex

/-!
# What `Interval` computes

CORA's `plus`, `linComb` and `mtimes` — the last at a plain matrix and at an
interval one — one file each, plus the constructor every other
representation's `interval` goes through: a box read off `2n` certified bounds.

`Point` and `CenterRadius` are the two readings of a box the enclosure proofs
elsewhere want: the degenerate one, and the centre-plus-deviation split.
-/
