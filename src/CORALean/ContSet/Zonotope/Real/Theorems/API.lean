import CORALean.ContSet.Zonotope.Real.Theorems.AbsBoundLeOfSubsetClosedBall
import CORALean.ContSet.Zonotope.Real.Theorems.AbsCoefficientLeOne
import CORALean.ContSet.Zonotope.Real.Theorems.AbsLeAbsBound
import CORALean.ContSet.Zonotope.Real.Theorems.AbsMaxOfPoint
import CORALean.ContSet.Zonotope.Real.Theorems.AbsMulLeOne
import CORALean.ContSet.Zonotope.Real.Theorems.AbsPairCoeffDiffLeOne
import CORALean.ContSet.Zonotope.Real.Theorems.AbsPairCoeffSumLeOne
import CORALean.ContSet.Zonotope.Real.Theorems.AbsWeightedLe
import CORALean.ContSet.Zonotope.Real.Theorems.AdaptSetOrderBudget
import CORALean.ContSet.Zonotope.Real.Theorems.AlignedWithOfSmul
import CORALean.ContSet.Zonotope.Real.Theorems.AutoTuneSetOrderLe
import CORALean.ContSet.Zonotope.Real.Theorems.BilinOuter
import CORALean.ContSet.Zonotope.Real.Theorems.CentreMemConstruct
import CORALean.ContSet.Zonotope.Real.Theorems.ClosedBallEq
import CORALean.ContSet.Zonotope.Real.Theorems.ClosedBallSubsetDiagonal
import CORALean.ContSet.Zonotope.Real.Theorems.Coefficient
import CORALean.ContSet.Zonotope.Real.Theorems.ContinuousAffine
import CORALean.ContSet.Zonotope.Real.Theorems.Convex
import CORALean.ContSet.Zonotope.Real.Theorems.CubeExact
import CORALean.ContSet.Zonotope.Real.Theorems.EnclGenSelSubset
import CORALean.ContSet.Zonotope.Real.Theorems.ExistsAutoTuneSetOrder
import CORALean.ContSet.Zonotope.Real.Theorems.FaceCentrallySymmetric
import CORALean.ContSet.Zonotope.Real.Theorems.GenNotRequiredIff
import CORALean.ContSet.Zonotope.Real.Theorems.GenRemovableIff
import CORALean.ContSet.Zonotope.Real.Theorems.HRepEq
import CORALean.ContSet.Zonotope.Real.Theorems.HRepInterEq
import CORALean.ContSet.Zonotope.Real.Theorems.HRepLinSubset
import CORALean.ContSet.Zonotope.Real.Theorems.HausdorffDist2IntervalLe
import CORALean.ContSet.Zonotope.Real.Theorems.HausdorffDist2IntervalLeCut
import CORALean.ContSet.Zonotope.Real.Theorems.HausdorffDist2IntervalLeMax
import CORALean.ContSet.Zonotope.Real.Theorems.HausdorffDist2LinCombLe
import CORALean.ContSet.Zonotope.Real.Theorems.HausdorffDist2ReduceByLe
import CORALean.ContSet.Zonotope.Real.Theorems.HausdorffDist2ReduceLe
import CORALean.ContSet.Zonotope.Real.Theorems.HausdorffDistIntervalLe
import CORALean.ContSet.Zonotope.Real.Theorems.IsBounded
import CORALean.ContSet.Zonotope.Real.Theorems.IsClosed
import CORALean.ContSet.Zonotope.Real.Theorems.IsCompact
import CORALean.ContSet.Zonotope.Real.Theorems.IsLUBNormFoldMaxAbsBound
import CORALean.ContSet.Zonotope.Real.Theorems.LinCombOuter
import CORALean.ContSet.Zonotope.Real.Theorems.LineClBasisIsUnitDet
import CORALean.ContSet.Zonotope.Real.Theorems.LineClKeepIsUnitDet
import CORALean.ContSet.Zonotope.Real.Theorems.LmtimesSingletonOuter
import CORALean.ContSet.Zonotope.Real.Theorems.MapExact
import CORALean.ContSet.Zonotope.Real.Theorems.MatMulLeftExact
import CORALean.ContSet.Zonotope.Real.Theorems.MatMulOuter
import CORALean.ContSet.Zonotope.Real.Theorems.MatMulRightExact
import CORALean.ContSet.Zonotope.Real.Theorems.MatPowOuter
import CORALean.ContSet.Zonotope.Real.Theorems.MemConstruct
import CORALean.ContSet.Zonotope.Real.Theorems.MemLinCombMtimesIff
import CORALean.ContSet.Zonotope.Real.Theorems.MethCVolumeLe
import CORALean.ContSet.Zonotope.Real.Theorems.MinkDiffAlignedExact
import CORALean.ContSet.Zonotope.Real.Theorems.MinkDiffAlignedInner
import CORALean.ContSet.Zonotope.Real.Theorems.MinkDiffAlignedNotInner
import CORALean.ContSet.Zonotope.Real.Theorems.MinkDiffAlignedOuter
import CORALean.ContSet.Zonotope.Real.Theorems.MinkDiffGenRecExact
import CORALean.ContSet.Zonotope.Real.Theorems.MinkDiffOrEmptyInner
import CORALean.ContSet.Zonotope.Real.Theorems.MinkDiffOrEmptyNeEmpty
import CORALean.ContSet.Zonotope.Real.Theorems.MinkDiffRepInner
import CORALean.ContSet.Zonotope.Real.Theorems.MinkDiffScaledInner
import CORALean.ContSet.Zonotope.Real.Theorems.MinkDiffStretchEq
import CORALean.ContSet.Zonotope.Real.Theorems.MinkDiffStretchInner
import CORALean.ContSet.Zonotope.Real.Theorems.MinkDiffStretchOuter
import CORALean.ContSet.Zonotope.Real.Theorems.MinkowskiDiffApplyLe
import CORALean.ContSet.Zonotope.Real.Theorems.MinkowskiDiffHRepEq
import CORALean.ContSet.Zonotope.Real.Theorems.MinkowskiDiffNotZonotope
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
import CORALean.ContSet.Zonotope.Real.Theorems.PlusIntervalExact
import CORALean.ContSet.Zonotope.Real.Theorems.PlusIntervalOuter
import CORALean.ContSet.Zonotope.Real.Theorems.PlusSubsetClosedBall
import CORALean.ContSet.Zonotope.Real.Theorems.ProjectExact
import CORALean.ContSet.Zonotope.Real.Theorems.ProjectHighDimExact
import CORALean.ContSet.Zonotope.Real.Theorems.QuadTaylorOuter
import CORALean.ContSet.Zonotope.Real.Theorems.RecentreSubMem
import CORALean.ContSet.Zonotope.Real.Theorems.RecentreZeroMem
import CORALean.ContSet.Zonotope.Real.Theorems.ReduceBoxAbsBoundLe
import CORALean.ContSet.Zonotope.Real.Theorems.ReduceBoxAntitone
import CORALean.ContSet.Zonotope.Real.Theorems.ReduceBoxEqOfPoint
import CORALean.ContSet.Zonotope.Real.Theorems.ReduceBoxErrorEqZero
import CORALean.ContSet.Zonotope.Real.Theorems.ReduceBoxOrderLe
import CORALean.ContSet.Zonotope.Real.Theorems.ReduceBoxOrderSpec
import CORALean.ContSet.Zonotope.Real.Theorems.ReduceByBasisOuter
import CORALean.ContSet.Zonotope.Real.Theorems.ReduceByOuter
import CORALean.ContSet.Zonotope.Real.Theorems.ReduceBySubsetAddBox
import CORALean.ContSet.Zonotope.Real.Theorems.ReduceCoOptDirOuter
import CORALean.ContSet.Zonotope.Real.Theorems.ReduceCoOptSVDOuter
import CORALean.ContSet.Zonotope.Real.Theorems.ReduceCombastelOrderLe
import CORALean.ContSet.Zonotope.Real.Theorems.ReduceCombastelOuter
import CORALean.ContSet.Zonotope.Real.Theorems.ReduceGirardOrderLe
import CORALean.ContSet.Zonotope.Real.Theorems.ReduceGirardOuter
import CORALean.ContSet.Zonotope.Real.Theorems.ReduceHybridPCOrderLe
import CORALean.ContSet.Zonotope.Real.Theorems.ReduceHybridPCOuter
import CORALean.ContSet.Zonotope.Real.Theorems.ReduceLineClOrderLe
import CORALean.ContSet.Zonotope.Real.Theorems.ReduceLineClOuter
import CORALean.ContSet.Zonotope.Real.Theorems.ReduceMethCOrderLe
import CORALean.ContSet.Zonotope.Real.Theorems.ReduceMethCOuter
import CORALean.ContSet.Zonotope.Real.Theorems.ReduceOrder
import CORALean.ContSet.Zonotope.Real.Theorems.ReduceOuter
import CORALean.ContSet.Zonotope.Real.Theorems.ReducePCAOrderLe
import CORALean.ContSet.Zonotope.Real.Theorems.ReducePCAOuter
import CORALean.ContSet.Zonotope.Real.Theorems.ReduceSignedInner
import CORALean.ContSet.Zonotope.Real.Theorems.ReduceSubsetAddBox
import CORALean.ContSet.Zonotope.Real.Theorems.ScaledRPI
import CORALean.ContSet.Zonotope.Real.Theorems.ShiftMemIff
import CORALean.ContSet.Zonotope.Real.Theorems.SplitIntersection
import CORALean.ContSet.Zonotope.Real.Theorems.SplitUnion
import CORALean.ContSet.Zonotope.Real.Theorems.SplitLongestGenUnion
import CORALean.ContSet.Zonotope.Real.Theorems.StepSubsetClosedBall
import CORALean.ContSet.Zonotope.Real.Theorems.StepSubsetClosedBallOfReduceBoxOrder
import CORALean.ContSet.Zonotope.Real.Theorems.SubsetClosedBallOfAbsBoundLe
import CORALean.ContSet.Zonotope.Real.Theorems.SubsetOfMulEqOneOfSumAbsLe
import CORALean.ContSet.Zonotope.Real.Theorems.SumDiagonalMul
import CORALean.ContSet.Zonotope.Real.Theorems.SumDiagonalMulCol
import CORALean.ContSet.Zonotope.Real.Theorems.SumPair
import CORALean.ContSet.Zonotope.Real.Theorems.SumSmulUpdate
import CORALean.ContSet.Zonotope.Real.Theorems.SumUnivReduceBy
import CORALean.ContSet.Zonotope.Real.Theorems.SupportBoundAttained
import CORALean.ContSet.Zonotope.Real.Theorems.IsFullDimIff
import CORALean.ContSet.Zonotope.Real.Theorems.RankEqFinrankIff
import CORALean.ContSet.Zonotope.Real.Theorems.RankEqIff
import CORALean.ContSet.Zonotope.Real.Theorems.RotateExact
import CORALean.ContSet.Zonotope.Real.Theorems.RotMatMulVecLeft
import CORALean.ContSet.Zonotope.Real.Theorems.RotMatMulVecRight
import CORALean.ContSet.Zonotope.Real.Theorems.RotMatMulVecOther
import CORALean.ContSet.Zonotope.Real.Theorems.UnderapproximateMem
import CORALean.ContSet.Zonotope.Real.Theorems.UnderapproximateConvexHullSubset
import CORALean.ContSet.Zonotope.Real.Theorems.RepresentsaPointIff
import CORALean.ContSet.Zonotope.Real.Theorems.RepresentsaOriginIff
import CORALean.ContSet.Zonotope.Real.Theorems.ExactPlusExact
import CORALean.ContSet.Zonotope.Real.Theorems.NormUbLe
import CORALean.ContSet.Zonotope.Real.Theorems.Radius2Bound
import CORALean.ContSet.Zonotope.Real.Theorems.NormSubCentreLeSumGeneratorLength
import CORALean.ContSet.Zonotope.Real.Theorems.ConstrSatSound
import CORALean.ContSet.Zonotope.Real.Theorems.CartProdExact
import CORALean.ContSet.Zonotope.Real.Theorems.SplitFirstGenUnion
import CORALean.ContSet.Zonotope.Real.Theorems.EnclosePolytopesOuter
import CORALean.ContSet.Zonotope.Real.Theorems.MethodCOuter
import CORALean.ContSet.Zonotope.Real.Theorems.OverApproxIndexLeIff
import CORALean.ContSet.Zonotope.Real.Theorems.ParallelotopeOuter
import CORALean.ContSet.Zonotope.Real.Theorems.HalfspaceRangeNonnegNotDisjoint
import CORALean.ContSet.Zonotope.Real.Theorems.HalfspaceRangeSound
import CORALean.ContSet.Zonotope.Real.Theorems.QuadMapMatZonoNotOuter
import CORALean.ContSet.Zonotope.Real.Theorems.QuadMapMatZonoOuter
import CORALean.ContSet.Zonotope.Real.Theorems.QuadMapOuter
import CORALean.ContSet.Zonotope.Real.Theorems.UnitIntervalMulOuter
import CORALean.ContSet.Zonotope.Real.Theorems.AndOuter
import CORALean.ContSet.Zonotope.Real.Theorems.IsequalConstruct
import CORALean.ContSet.Zonotope.Real.Theorems.FilterGenConstruct
import CORALean.ContSet.Zonotope.Real.Theorems.CompactZerosExact

/-!
# What `Zonotope` guarantees

`plus` and `map` exactly, `reduce` and the interval hull as enclosures, plus what a set-valued
integral needs. `MemConstruct` reads membership coordinatewise, `Coefficient` holds the proof
devices the float layer shares; `BilinOuter`, `MtimesMatZonotopeOuter`, `QuadTaylorOuter` are a
matrix zonotope on a set, never exact — `OfPointMem`/`Recentre`/`AbsMaxOfPoint` are what those ask.
`MinkDiffAlignedInner` and `MinkDiffRepInner` run the reverse, at aligned and at represented
generators; `MinkDiffAlignedOuter` closes the first to `MinkDiffAlignedExact`, whose scaling
`MinkDiffAlignedNotInner` holds to `[0, 1]` and whose pairing `AlignedWithOfSmul` reads back as the
alignment relation. `MinkDiffStretchInner` and `MinkDiffStretchOuter` are Althoff's two linear-
programming approximations, each in its own direction and each wanting a halfspace description of
the minuend that `MinkowskiDiffApplyLe` does without — `MinkowskiDiffHRepEq` is `Thm. 3`;
`EnclGenSelSubset` keeps his generator selection inside the minuend. `MinkDiffOrEmptyInner` carries
`minkDiffRep` through `MinkDiff`'s wrapper, `MinkDiffOrEmptyNeEmpty` says it is never empty, and
`MinkDiffGenRecExact` alone is exact everywhere. `MtimesIntervalMatSubsetClosedBall` bounds a
product, `MtimesIntervalMatSymmBox` it at a symmetric matrix. `ReduceBySubsetAddBox` is
`ReduceByOuter` backwards — the reduced set sits inside the original plus its box — carried to
`reduce` by `ReduceSubsetAddBox`, cancelled again by `MinkowskiDiffReduceByBoxInner` on
`CentreMemConstruct`'s nonemptiness, and priced by `HausdorffDistIntervalLe` at the sup norm and the
`HausdorffDist2*` group at `‖·‖₂`. `SubsetClosedBallOfAbsBoundLe` and its converse tie `absBound` to
a sup-norm ball, which `MtimesSubsetClosedBall`, `PlusSubsetClosedBall` and `ReduceBoxAbsBoundLe`
carry through their operations, `StepSubsetClosedBall` composes at `reach`'s shape, and
`SumSmulUpdate` is the sum a split changes, read by `SplitUnion`/`SplitIntersection`.
-/
