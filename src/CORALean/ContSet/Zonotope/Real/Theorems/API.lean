import CORALean.ContSet.Zonotope.Real.Theorems.MemConstruct
import CORALean.ContSet.Zonotope.Real.Theorems.OfPointMem
import CORALean.ContSet.Zonotope.Real.Theorems.AbsMaxOfPoint
import CORALean.ContSet.Zonotope.Real.Theorems.RecentreZeroMem
import CORALean.ContSet.Zonotope.Real.Theorems.RecentreSubMem
import CORALean.ContSet.Zonotope.Real.Theorems.CentreMemConstruct
import CORALean.ContSet.Zonotope.Real.Theorems.Coefficient
import CORALean.ContSet.Zonotope.Real.Theorems.AbsCoefficientLeOne
import CORALean.ContSet.Zonotope.Real.Theorems.MulCoefficient
import CORALean.ContSet.Zonotope.Real.Theorems.AbsMulLeOne
import CORALean.ContSet.Zonotope.Real.Theorems.SumDiagonalMul
import CORALean.ContSet.Zonotope.Real.Theorems.SumDiagonalMulCol
import CORALean.ContSet.Zonotope.Real.Theorems.PlusExact
import CORALean.ContSet.Zonotope.Real.Theorems.MapExact
import CORALean.ContSet.Zonotope.Real.Theorems.MtimesExact
import CORALean.ContSet.Zonotope.Real.Theorems.LmtimesSingletonOuter
import CORALean.ContSet.Zonotope.Real.Theorems.MatMulLeftExact
import CORALean.ContSet.Zonotope.Real.Theorems.MatMulRightExact
import CORALean.ContSet.Zonotope.Real.Theorems.Convex
import CORALean.ContSet.Zonotope.Real.Theorems.IsBounded
import CORALean.ContSet.Zonotope.Real.Theorems.ClosedBallEq
import CORALean.ContSet.Zonotope.Real.Theorems.ContinuousAffine
import CORALean.ContSet.Zonotope.Real.Theorems.IsCompact
import CORALean.ContSet.Zonotope.Real.Theorems.IsClosed
import CORALean.ContSet.Zonotope.Real.Theorems.PairCoeffSum
import CORALean.ContSet.Zonotope.Real.Theorems.PairCoeffDiff
import CORALean.ContSet.Zonotope.Real.Theorems.AbsWeightedLe
import CORALean.ContSet.Zonotope.Real.Theorems.AbsPairCoeffSumLeOne
import CORALean.ContSet.Zonotope.Real.Theorems.AbsPairCoeffDiffLeOne
import CORALean.ContSet.Zonotope.Real.Theorems.SumPair
import CORALean.ContSet.Zonotope.Real.Theorems.LinCombOuter
import CORALean.ContSet.Zonotope.Real.Theorems.AbsLeAbsBound
import CORALean.ContSet.Zonotope.Real.Theorems.MtimesIntervalMatOuter
import CORALean.ContSet.Zonotope.Real.Theorems.BilinOuter
import CORALean.ContSet.Zonotope.Real.Theorems.MtimesMatZonotopeOuter
import CORALean.ContSet.Zonotope.Real.Theorems.MatMulOuter
import CORALean.ContSet.Zonotope.Real.Theorems.MatPowOuter
import CORALean.ContSet.Zonotope.Real.Theorems.SumUnivReduceBy
import CORALean.ContSet.Zonotope.Real.Theorems.ReduceByOuter
import CORALean.ContSet.Zonotope.Real.Theorems.ReduceSubsetAddBox
import CORALean.ContSet.Zonotope.Real.Theorems.ReduceBySubsetAddBox
import CORALean.ContSet.Zonotope.Real.Theorems.MinkowskiDiffReduceByBoxInner
import CORALean.ContSet.Zonotope.Real.Theorems.ReduceGirardOuter
import CORALean.ContSet.Zonotope.Real.Theorems.ReduceCombastelOuter
import CORALean.ContSet.Zonotope.Real.Theorems.ReduceOuter
import CORALean.ContSet.Zonotope.Real.Theorems.ReduceGirardOrderLe
import CORALean.ContSet.Zonotope.Real.Theorems.ReduceCombastelOrderLe
import CORALean.ContSet.Zonotope.Real.Theorems.ReduceOrder
import CORALean.ContSet.Zonotope.Real.Theorems.MinkDiffAlignedInner
import CORALean.ContSet.Zonotope.Real.Theorems.MinkDiffRepInner
import CORALean.ContSet.Zonotope.Real.Theorems.MinkDiffOrEmptyInner
import CORALean.ContSet.Zonotope.Real.Theorems.MinkDiffOrEmptyNeEmpty

/-!
# What `Zonotope` guarantees

`plus` and `map` exactly, `reduce` and the interval hull as enclosures, and the
topological facts a set-valued integral needs. `MemConstruct` reads membership
coordinatewise, which is what every one of them is stated against, and
`Coefficient` with the two facts about it holds the shared proof devices, which
the float layer needs too. `BilinOuter` and `MtimesMatZonotopeOuter` are a
matrix zonotope acting on a set, an enclosure and never exact. `OfPointMem`
and the two `Recentre` facts are what those classes ask of a zonotope, and
`AbsMaxOfPoint` reads the interval hull of a point back as the point.
`MinkDiffAlignedInner` and `MinkDiffRepInner` are the two guarantees running
the other way, the first exact at aligned generators and the second sound at
any representation of the subtrahend's generators in the minuend's.
`MinkDiffOrEmptyInner` carries the second through the wrapper `MinkDiff` needs,
and `MinkDiffOrEmptyNeEmpty` says that wrapper is not empty every time.

`ReduceBySubsetAddBox` is `ReduceByOuter` run backwards — the reduced zonotope
sits inside the original plus the box it introduced — `ReduceSubsetAddBox`
carries that to the `reduce` an algorithm calls, no-op branch included, and
`MinkowskiDiffReduceByBoxInner` cancels the box off again — the one guarantee
here reading an enclosure backwards rather than starting from a Minkowski
difference. `CentreMemConstruct` says a zonotope is nonempty, which every such
cancellation asks of the set it cancels.
-/
