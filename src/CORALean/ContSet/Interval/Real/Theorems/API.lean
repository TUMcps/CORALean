import CORALean.ContSet.Interval.Real.Theorems.MemMat
import CORALean.ContSet.Interval.Real.Theorems.Convex
import CORALean.ContSet.Interval.Real.Theorems.IsBounded
import CORALean.ContSet.Interval.Real.Theorems.IsClosed
import CORALean.ContSet.Interval.Real.Theorems.IsCompact
import CORALean.ContSet.Interval.Real.Theorems.IsNonempty
import CORALean.ContSet.Interval.Real.Theorems.NotIsNonempty
import CORALean.ContSet.Interval.Real.Theorems.AbsSubCenterLe
import CORALean.ContSet.Interval.Real.Theorems.PlusOuter
import CORALean.ContSet.Interval.Real.Theorems.PlusExact
import CORALean.ContSet.Interval.Real.Theorems.MinkDiffInner
import CORALean.ContSet.Interval.Real.Theorems.MinkDiffExact
import CORALean.ContSet.Interval.Real.Theorems.MulBetweenEndpoints
import CORALean.ContSet.Interval.Real.Theorems.MulBetweenCorners
import CORALean.ContSet.Interval.Real.Theorems.LinCombOuter
import CORALean.ContSet.Interval.Real.Theorems.MemCenter
import CORALean.ContSet.Interval.Real.Theorems.MemPoint
import CORALean.ContSet.Interval.Real.Theorems.RecentreZeroMem
import CORALean.ContSet.Interval.Real.Theorems.RecentreSubMem
import CORALean.ContSet.Interval.Real.Theorems.MtimesIntervalMatOuter
import CORALean.ContSet.Interval.Real.Theorems.MatMulOuter
import CORALean.ContSet.Interval.Real.Theorems.MatMulSymmPoint
import CORALean.ContSet.Interval.Real.Theorems.MatPowOuter
import CORALean.ContSet.Interval.Real.Theorems.SmulOuter
import CORALean.ContSet.Interval.Real.Theorems.NormLeAbsMax
import CORALean.ContSet.Interval.Real.Theorems.MtimesIsNonempty
import CORALean.ContSet.Interval.Real.Theorems.MtimesOuter
import CORALean.ContSet.Interval.Real.Theorems.MtimesWidth
import CORALean.ContSet.Interval.Real.Theorems.ReindexExact
import CORALean.ContSet.Interval.Real.Theorems.SplitAtCover
import CORALean.ContSet.Interval.Real.Theorems.HausdorffDist2AddLeBoxRadius

/-!
# What `Interval` guarantees

An enclosure per operation — `plus` exactly so, `minkDiff` exactly so and inner,
unconditionally — and the topological facts a set-valued integral needs:
convex, closed, bounded, and the two last combined into the compactness an
interface field asks for. `MemMat` is membership at an interval matrix, read by
row and column, and `MemCenter` is the one point a box always offers a layer
that has to commit to a value. `RecentreZeroMem`/`RecentreSubMem` need that
same nonemptiness to place the origin, a crossed box denoting `∅` instead.
`MtimesIsNonempty` is why an image box needs no hypothesis before it is used
as one. `MtimesWidth` is how far apart its bounds are, for an error tolerance.
`MulBetweenCorners` is the scalar fact `mtimes*` products against an interval
matrix share, and `MatMulOuter` is its use on `matMul`, an enclosure and not an
equality since a product entry's `k`-summands are bounded independently.
`MatMulSymmPoint` is the case that loses nothing: a symmetric left factor
against a point right one collapses to `|M|` scaled by the radius. `MatPowOuter`
lifts the general bound along `matPow`'s recursion, growing the same dependency
loss with every power. `SmulOuter` is `MulBetweenEndpoints` read back through
`Entrywise`. `SplitAtCover` is why `splitAt` is sound to feed
`NeuralNetwork.holds_of_split`: its two halves cover the box they bisected.
`NormLeAbsMax` bounds the `l∞` operator norm uniformly over a box by its
`AbsMax`, an exponential enclosure's own requirement. `HausdorffDist2AddLeBoxRadius`
bounds a Minkowski sum's move by any box enclosing what got added.
-/
