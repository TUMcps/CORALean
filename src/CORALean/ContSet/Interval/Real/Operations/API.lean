import CORALean.ContSet.Interval.Real.Operations.And
import CORALean.ContSet.Interval.Real.Operations.Plus
import CORALean.ContSet.Interval.Real.Operations.LinComb
import CORALean.ContSet.Interval.Real.Operations.Mtimes
import CORALean.ContSet.Interval.Real.Operations.MtimesIntervalMat
import CORALean.ContSet.Interval.Real.Operations.OfBounds

/-!
# What `Interval` computes

CORA's `plus`, `linComb` and `mtimes` — the last at a plain matrix and at an
interval one — one file each, plus the constructor every other
representation's `interval` goes through: a box read off `2n` certified bounds.
-/
