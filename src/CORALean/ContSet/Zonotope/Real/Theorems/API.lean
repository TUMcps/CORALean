import CORALean.ContSet.Zonotope.Real.Theorems.AbsBoundLeOfSubsetClosedBall
import CORALean.ContSet.Zonotope.Real.Theorems.AbsCoefficientLeOne
import CORALean.ContSet.Zonotope.Real.Theorems.AbsLeAbsBound
import CORALean.ContSet.Zonotope.Real.Theorems.AbsMaxOfPoint
import CORALean.ContSet.Zonotope.Real.Theorems.AbsMulLeOne
import CORALean.ContSet.Zonotope.Real.Theorems.AbsPairCoeffDiffLeOne
import CORALean.ContSet.Zonotope.Real.Theorems.AbsPairCoeffSumLeOne
import CORALean.ContSet.Zonotope.Real.Theorems.AbsWeightedLe
import CORALean.ContSet.Zonotope.Real.Theorems.BilinOuter
import CORALean.ContSet.Zonotope.Real.Theorems.CentreMemConstruct
import CORALean.ContSet.Zonotope.Real.Theorems.ClosedBallEq
import CORALean.ContSet.Zonotope.Real.Theorems.Coefficient
import CORALean.ContSet.Zonotope.Real.Theorems.ContinuousAffine
import CORALean.ContSet.Zonotope.Real.Theorems.Convex
import CORALean.ContSet.Zonotope.Real.Theorems.HausdorffDist2IntervalLe
import CORALean.ContSet.Zonotope.Real.Theorems.HausdorffDistIntervalLe
import CORALean.ContSet.Zonotope.Real.Theorems.IsBounded
import CORALean.ContSet.Zonotope.Real.Theorems.IsClosed
import CORALean.ContSet.Zonotope.Real.Theorems.IsCompact
import CORALean.ContSet.Zonotope.Real.Theorems.LinCombOuter
import CORALean.ContSet.Zonotope.Real.Theorems.LmtimesSingletonOuter
import CORALean.ContSet.Zonotope.Real.Theorems.MapExact
import CORALean.ContSet.Zonotope.Real.Theorems.MatMulLeftExact
import CORALean.ContSet.Zonotope.Real.Theorems.MatMulOuter
import CORALean.ContSet.Zonotope.Real.Theorems.MatMulRightExact
import CORALean.ContSet.Zonotope.Real.Theorems.MatPowOuter
import CORALean.ContSet.Zonotope.Real.Theorems.MemConstruct
import CORALean.ContSet.Zonotope.Real.Theorems.MethCVolumeLe
import CORALean.ContSet.Zonotope.Real.Theorems.MinkDiffAlignedExact
import CORALean.ContSet.Zonotope.Real.Theorems.MinkDiffAlignedInner
import CORALean.ContSet.Zonotope.Real.Theorems.MinkDiffAlignedNotInner
import CORALean.ContSet.Zonotope.Real.Theorems.MinkDiffAlignedOuter
import CORALean.ContSet.Zonotope.Real.Theorems.MinkDiffGenRecExact
import CORALean.ContSet.Zonotope.Real.Theorems.MinkDiffOrEmptyInner
import CORALean.ContSet.Zonotope.Real.Theorems.MinkDiffOrEmptyNeEmpty
import CORALean.ContSet.Zonotope.Real.Theorems.MinkDiffRepInner
import CORALean.ContSet.Zonotope.Real.Theorems.MinkowskiDiffReduceByBoxInner
import CORALean.ContSet.Zonotope.Real.Theorems.MtimesExact
import CORALean.ContSet.Zonotope.Real.Theorems.MtimesIntervalMatOuter
import CORALean.ContSet.Zonotope.Real.Theorems.MtimesIntervalMatSubsetClosedBall
import CORALean.ContSet.Zonotope.Real.Theorems.MtimesIntervalMatSymmBox
import CORALean.ContSet.Zonotope.Real.Theorems.MtimesMatZonotopeOuter
import CORALean.ContSet.Zonotope.Real.Theorems.MtimesSubsetClosedBall
import CORALean.ContSet.Zonotope.Real.Theorems.MulCoefficient
import CORALean.ContSet.Zonotope.Real.Theorems.OfPointMem
import CORALean.ContSet.Zonotope.Real.Theorems.OfPointMemIff
import CORALean.ContSet.Zonotope.Real.Theorems.PCABasisIsUnitDet
import CORALean.ContSet.Zonotope.Real.Theorems.PCACovarianceIsHermitian
import CORALean.ContSet.Zonotope.Real.Theorems.PairCoeffDiff
import CORALean.ContSet.Zonotope.Real.Theorems.PairCoeffSum
import CORALean.ContSet.Zonotope.Real.Theorems.PlusExact
import CORALean.ContSet.Zonotope.Real.Theorems.PlusIntervalOuter
import CORALean.ContSet.Zonotope.Real.Theorems.PlusSubsetClosedBall
import CORALean.ContSet.Zonotope.Real.Theorems.RecentreSubMem
import CORALean.ContSet.Zonotope.Real.Theorems.RecentreZeroMem
import CORALean.ContSet.Zonotope.Real.Theorems.ReduceBoxAbsBoundLe
import CORALean.ContSet.Zonotope.Real.Theorems.ReduceBoxAntitone
import CORALean.ContSet.Zonotope.Real.Theorems.ReduceBoxEqOfPoint
import CORALean.ContSet.Zonotope.Real.Theorems.ReduceBoxOrderLe
import CORALean.ContSet.Zonotope.Real.Theorems.ReduceBoxOrderSpec
import CORALean.ContSet.Zonotope.Real.Theorems.ReduceByBasisOuter
import CORALean.ContSet.Zonotope.Real.Theorems.ReduceByOuter
import CORALean.ContSet.Zonotope.Real.Theorems.ReduceBySubsetAddBox
import CORALean.ContSet.Zonotope.Real.Theorems.ReduceCombastelOrderLe
import CORALean.ContSet.Zonotope.Real.Theorems.ReduceCombastelOuter
import CORALean.ContSet.Zonotope.Real.Theorems.ReduceGirardOrderLe
import CORALean.ContSet.Zonotope.Real.Theorems.ReduceGirardOuter
import CORALean.ContSet.Zonotope.Real.Theorems.ReduceMethCOrderLe
import CORALean.ContSet.Zonotope.Real.Theorems.ReduceMethCOuter
import CORALean.ContSet.Zonotope.Real.Theorems.ReduceOrder
import CORALean.ContSet.Zonotope.Real.Theorems.ReduceOuter
import CORALean.ContSet.Zonotope.Real.Theorems.ReducePCAOrderLe
import CORALean.ContSet.Zonotope.Real.Theorems.ReducePCAOuter
import CORALean.ContSet.Zonotope.Real.Theorems.ReduceSubsetAddBox
import CORALean.ContSet.Zonotope.Real.Theorems.SplitIntersection
import CORALean.ContSet.Zonotope.Real.Theorems.SplitUnion
import CORALean.ContSet.Zonotope.Real.Theorems.StepSubsetClosedBall
import CORALean.ContSet.Zonotope.Real.Theorems.StepSubsetClosedBallOfReduceBoxOrder
import CORALean.ContSet.Zonotope.Real.Theorems.SubsetClosedBallOfAbsBoundLe
import CORALean.ContSet.Zonotope.Real.Theorems.SumDiagonalMul
import CORALean.ContSet.Zonotope.Real.Theorems.SumDiagonalMulCol
import CORALean.ContSet.Zonotope.Real.Theorems.SumPair
import CORALean.ContSet.Zonotope.Real.Theorems.SumSmulUpdate
import CORALean.ContSet.Zonotope.Real.Theorems.SumUnivReduceBy
import CORALean.ContSet.Zonotope.Real.Theorems.SupportBoundAttained

/-!
# What `Zonotope` guarantees

`plus` and `map` exactly, `reduce` and the interval hull as enclosures, and the topological facts a
set-valued integral needs. `MemConstruct` reads membership coordinatewise, and `Coefficient` holds
the shared proof devices the float layer needs too. `BilinOuter` and `MtimesMatZonotopeOuter` are a
matrix zonotope acting on a set, never exact; `OfPointMem`, `Recentre` and `AbsMaxOfPoint` are what
those classes ask. `MinkDiffAlignedInner` and `MinkDiffRepInner` run the reverse, at aligned and at
represented generators; `MinkDiffAlignedOuter` closes the first to `MinkDiffAlignedExact`, whose
scaling `MinkDiffAlignedNotInner` holds to `[0, 1]`. `MinkDiffOrEmptyInner` carries the second
through `MinkDiff`'s wrapper, `MinkDiffOrEmptyNeEmpty` says it is never empty, and
`MinkDiffGenRecExact` alone is exact at every input. `MtimesIntervalMatSubsetClosedBall` bounds a
product above, `MtimesIntervalMatSymmBox` it at a symmetric matrix: `S · box(Z)`.

`ReduceBySubsetAddBox` is `ReduceByOuter` backwards — the reduced zonotope sits inside the original
plus the box it introduced — carried to `reduce` itself by `ReduceSubsetAddBox`;
`MinkowskiDiffReduceByBoxInner` cancels the box off again and `CentreMemConstruct` says a zonotope
is nonempty, which every cancellation needs. `HausdorffDistIntervalLe` prices that box instead: its
distance to the zonotope is at most the generators' total length, and `HausdorffDist2IntervalLe` is
that bound at `‖·‖₂`. `SubsetClosedBallOfAbsBoundLe` and its converse relate `absBound` to a
sup-norm ball; `MtimesSubsetClosedBall`, `PlusSubsetClosedBall` and `ReduceBoxAbsBoundLe` carry one
through `mtimes`, `plus` and `reduceBox`, and `StepSubsetClosedBall` composes them at `reach`'s
shape, its box term discharged crudely or, via `reduceBoxOrder`, sharply. `SumSmulUpdate` is the
one sum a split changes a term of, which `SplitUnion` and `SplitIntersection` read both halves off.
-/
