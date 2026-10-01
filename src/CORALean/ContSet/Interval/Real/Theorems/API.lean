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
import CORALean.ContSet.Interval.Real.Theorems.DivBetweenEndpoints
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
import CORALean.ContSet.Interval.Real.Theorems.SupportBoundEntrywiseAttained
import CORALean.ContSet.Interval.Real.Theorems.SupportBoundAttained
import CORALean.ContSet.Interval.Real.Theorems.MtimesOuter
import CORALean.ContSet.Interval.Real.Theorems.MtimesWidth
import CORALean.ContSet.Interval.Real.Theorems.ReindexExact
import CORALean.ContSet.Interval.Real.Theorems.SplitAtCover
import CORALean.ContSet.Interval.Real.Theorems.HausdorffDist2AddLeBoxRadius
import CORALean.ContSet.Interval.Real.Theorems.UminusExact
import CORALean.ContSet.Interval.Real.Theorems.UplusExact
import CORALean.ContSet.Interval.Real.Theorems.MinusEqPlusUminus
import CORALean.ContSet.Interval.Real.Theorems.MinusOuter
import CORALean.ContSet.Interval.Real.Theorems.MinusExact
import CORALean.ContSet.Interval.Real.Theorems.InfimumMemConstruct
import CORALean.ContSet.Interval.Real.Theorems.SupremumMemConstruct
import CORALean.ContSet.Interval.Real.Theorems.OrOuter
import CORALean.ContSet.Interval.Real.Theorems.ConvHullOuter
import CORALean.ContSet.Interval.Real.Theorems.EnclosePointsOuter
import CORALean.ContSet.Interval.Real.Theorems.OriginExact
import CORALean.ContSet.Interval.Real.Theorems.AbsExact
import CORALean.ContSet.Interval.Real.Theorems.ConstructEqSingleton
import CORALean.ContSet.Interval.Real.Theorems.EmptyExact
import CORALean.ContSet.Interval.Real.Theorems.ExistsMulEq
import CORALean.ContSet.Interval.Real.Theorems.ExpExact
import CORALean.ContSet.Interval.Real.Theorems.MonotoneImageExact
import CORALean.ContSet.Interval.Real.Theorems.AntitoneImageExact
import CORALean.ContSet.Interval.Real.Theorems.MonotoneImageOuter
import CORALean.ContSet.Interval.Real.Theorems.SqrtExact
import CORALean.ContSet.Interval.Real.Theorems.LogExact
import CORALean.ContSet.Interval.Real.Theorems.AtanExact
import CORALean.ContSet.Interval.Real.Theorems.SinhExact
import CORALean.ContSet.Interval.Real.Theorems.AsinhExact
import CORALean.ContSet.Interval.Real.Theorems.TanhExact
import CORALean.ContSet.Interval.Real.Theorems.AsinExact
import CORALean.ContSet.Interval.Real.Theorems.AcosExact
import CORALean.ContSet.Interval.Real.Theorems.SignMonotone
import CORALean.ContSet.Interval.Real.Theorems.SignOuter
import CORALean.ContSet.Interval.Real.Theorems.RoundOuter
import CORALean.ContSet.Interval.Real.Theorems.LeIffSubset
import CORALean.ContSet.Interval.Real.Theorems.LeSubset
import CORALean.ContSet.Interval.Real.Theorems.LtSubset
import CORALean.ContSet.Interval.Real.Theorems.ProjectExact
import CORALean.ContSet.Interval.Real.Theorems.ProjectHighDimExact
import CORALean.ContSet.Interval.Real.Theorems.ProjectOuter
import CORALean.ContSet.Interval.Real.Theorems.RepresentsaEmptySetIff
import CORALean.ContSet.Interval.Real.Theorems.RepresentsaOriginIff
import CORALean.ContSet.Interval.Real.Theorems.RepresentsaPointIff
import CORALean.ContSet.Interval.Real.Theorems.SingletonOfInfEqSup
import CORALean.ContSet.Interval.Real.Theorems.TimesExact
import CORALean.ContSet.Interval.Real.Theorems.TimesOuter
import CORALean.ContSet.Interval.Real.Theorems.VolumeEq
import CORALean.ContSet.Interval.Real.Theorems.IsFullDimIff
import CORALean.ContSet.Interval.Real.Theorems.NormLe
import CORALean.ContSet.Interval.Real.Theorems.NormAttained

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
`DivBetweenEndpoints` solves `MulBetweenEndpoints` back for the point. `MulBetweenCorners` is
the scalar fact `mtimes*` products against an interval matrix share, and `MatMulOuter` is its
use on `matMul`, an enclosure since a product's `k`-summands bound independently.
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
