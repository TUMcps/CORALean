import CORALean.ContSet.PolyZonotope.Float.Operations.SplitLongestGen
import CORALean.ContSet.PolyZonotope.Float.Operations.LongestFactor
import CORALean.ContSet.PolyZonotope.Float.Operations.SplitDepFactor
import CORALean.ContSet.PolyZonotope.Float.Operations.Resolve
import CORALean.ContSet.PolyZonotope.Float.Operations.GetSubset
import CORALean.ContSet.PolyZonotope.Float.Operations.GetSubsetGDiff
import CORALean.ContSet.PolyZonotope.Float.Operations.GetSubsetGDown
import CORALean.ContSet.PolyZonotope.Float.Operations.GetSubsetCoef
import CORALean.ContSet.PolyZonotope.Float.Operations.MaxExp
import CORALean.ContSet.PolyZonotope.Float.Operations.Isequal
import CORALean.ContSet.PolyZonotope.Float.Operations.GeneratorError
import CORALean.ContSet.PolyZonotope.Float.Operations.CenterResidual
import CORALean.ContSet.PolyZonotope.Float.Operations.Centre
import CORALean.ContSet.PolyZonotope.Float.Operations.Plus
import CORALean.ContSet.PolyZonotope.Float.Operations.ExactPlus
import CORALean.ContSet.PolyZonotope.Float.Operations.MtimesResidual
import CORALean.ContSet.PolyZonotope.Float.Operations.Mtimes
import CORALean.ContSet.PolyZonotope.Float.Operations.RepKeep
import CORALean.ContSet.PolyZonotope.Float.Operations.SupportBound
import CORALean.ContSet.PolyZonotope.Float.Operations.KeepIdx
import CORALean.ContSet.PolyZonotope.Float.Operations.RepTab
import CORALean.ContSet.PolyZonotope.Float.Operations.KeepTab
import CORALean.ContSet.PolyZonotope.Float.Operations.TabAt
import CORALean.ContSet.PolyZonotope.Float.Operations.FiberDown
import CORALean.ContSet.PolyZonotope.Float.Operations.FiberUp
import CORALean.ContSet.PolyZonotope.Float.Operations.MergedCol
import CORALean.ContSet.PolyZonotope.Float.Operations.MergedColUp
import CORALean.ContSet.PolyZonotope.Float.Operations.CompactGap
import CORALean.ContSet.PolyZonotope.Float.Operations.CompactGens
import CORALean.ContSet.PolyZonotope.Float.Operations.CompactFactors
import CORALean.ContSet.PolyZonotope.Float.Operations.Compact
import CORALean.ContSet.PolyZonotope.Float.Operations.ErrorBound
import CORALean.ContSet.PolyZonotope.Float.Operations.Dependent
import CORALean.ContSet.PolyZonotope.Float.Operations.Midpoint
import CORALean.ContSet.PolyZonotope.Float.Operations.HalfDiff
import CORALean.ContSet.PolyZonotope.Float.Operations.MidpointResidual
import CORALean.ContSet.PolyZonotope.Float.Operations.HalfDiffError
import CORALean.ContSet.PolyZonotope.Float.Operations.LinCombGI
import CORALean.ContSet.PolyZonotope.Float.Operations.LinCombGIDiff
import CORALean.ContSet.PolyZonotope.Float.Operations.LinComb
import CORALean.ContSet.PolyZonotope.Float.Operations.ExtG
import CORALean.ContSet.PolyZonotope.Float.Operations.ExtE
import CORALean.ContSet.PolyZonotope.Float.Operations.QuadMapE
import CORALean.ContSet.PolyZonotope.Float.Operations.QuadDown
import CORALean.ContSet.PolyZonotope.Float.Operations.QuadUp
import CORALean.ContSet.PolyZonotope.Float.Operations.QuadMapGDown
import CORALean.ContSet.PolyZonotope.Float.Operations.QuadMapGUp
import CORALean.ContSet.PolyZonotope.Float.Operations.QuadMapGDiff
import CORALean.ContSet.PolyZonotope.Float.Operations.QuadMapDep
import CORALean.ContSet.PolyZonotope.Float.Operations.QuadMap
import CORALean.ContSet.PolyZonotope.Float.Operations.BilinE
import CORALean.ContSet.PolyZonotope.Float.Operations.BilinGDown
import CORALean.ContSet.PolyZonotope.Float.Operations.BilinGUp
import CORALean.ContSet.PolyZonotope.Float.Operations.BilinGDiff
import CORALean.ContSet.PolyZonotope.Float.Operations.Bilin
import CORALean.ContSet.PolyZonotope.Float.Operations.MixedForm
import CORALean.ContSet.PolyZonotope.Float.Operations.QuadMapMixed
import CORALean.ContSet.PolyZonotope.Float.Operations.MulGDown
import CORALean.ContSet.PolyZonotope.Float.Operations.MulGUp
import CORALean.ContSet.PolyZonotope.Float.Operations.MulGDiff
import CORALean.ContSet.PolyZonotope.Float.Operations.MulE
import CORALean.ContSet.PolyZonotope.Float.Operations.Mul
import CORALean.ContSet.PolyZonotope.Float.Operations.NominalSupportBound
import CORALean.ContSet.PolyZonotope.Float.Operations.NoIndep
import CORALean.ContSet.PolyZonotope.Float.Operations.EvalPolyBoundS
import CORALean.ContSet.PolyZonotope.Float.Operations.EvalPolyStep
import CORALean.ContSet.PolyZonotope.Float.Operations.EvalPolyP
import CORALean.ContSet.PolyZonotope.Float.Operations.EvalPoly
import CORALean.ContSet.PolyZonotope.Float.Operations.EvalPolyFactorCount
import CORALean.ContSet.PolyZonotope.Float.Operations.DropRadius
import CORALean.ContSet.PolyZonotope.Float.Operations.ReduceBy
import CORALean.ContSet.PolyZonotope.Float.Operations.GirardMetric
import CORALean.ContSet.PolyZonotope.Float.Operations.GirardSplit
import CORALean.ContSet.PolyZonotope.Float.Operations.ReduceGirard
import CORALean.ContSet.PolyZonotope.Float.Operations.ReduceGirardDependent
import CORALean.ContSet.PolyZonotope.Float.Operations.Reduce
import CORALean.ContSet.PolyZonotope.Float.Operations.ReduceDependent
import CORALean.ContSet.PolyZonotope.Float.Operations.MergedGen
import CORALean.ContSet.PolyZonotope.Float.Operations.RelaxWidth
import CORALean.ContSet.PolyZonotope.Float.Operations.RelaxGen
import CORALean.ContSet.PolyZonotope.Float.Operations.RelaxGap
import CORALean.ContSet.PolyZonotope.Float.Operations.RelaxExp
import CORALean.ContSet.PolyZonotope.Float.Operations.RelaxGenEven
import CORALean.ContSet.PolyZonotope.Float.Operations.RelaxGenEvenUp
import CORALean.ContSet.PolyZonotope.Float.Operations.RelaxCentreEven
import CORALean.ContSet.PolyZonotope.Float.Operations.RelaxGapEven
import CORALean.ContSet.PolyZonotope.Float.Operations.RelaxExpEven
import CORALean.ContSet.PolyZonotope.Float.Operations.RelaxDrift
import CORALean.ContSet.PolyZonotope.Float.Operations.RelaxShiftMid
import CORALean.ContSet.PolyZonotope.Float.Operations.RelaxShiftMidUp
import CORALean.ContSet.PolyZonotope.Float.Operations.RelaxGenMid
import CORALean.ContSet.PolyZonotope.Float.Operations.RelaxGenMidUp
import CORALean.ContSet.PolyZonotope.Float.Operations.RelaxCentreMid
import CORALean.ContSet.PolyZonotope.Float.Operations.RelaxGapMid
import CORALean.ContSet.PolyZonotope.Float.Operations.RelaxExpMid
import CORALean.ContSet.PolyZonotope.Float.Operations.RelaxWidthMulti
import CORALean.ContSet.PolyZonotope.Float.Operations.RelaxGenMulti
import CORALean.ContSet.PolyZonotope.Float.Operations.RelaxGapMulti
import CORALean.ContSet.PolyZonotope.Float.Operations.RelaxExpMulti
import CORALean.ContSet.PolyZonotope.Float.Operations.RelaxExpGreedy
import CORALean.ContSet.PolyZonotope.Float.Operations.Origin
import CORALean.ContSet.PolyZonotope.Float.Operations.PadBack
import CORALean.ContSet.PolyZonotope.Float.Operations.Reindex
import CORALean.ContSet.PolyZonotope.Float.Operations.Restructure
import CORALean.ContSet.PolyZonotope.Float.Operations.Project
import CORALean.ContSet.PolyZonotope.Float.Operations.CartProd
import CORALean.ContSet.PolyZonotope.Float.Operations.BlockPadLeft
import CORALean.ContSet.PolyZonotope.Float.Operations.BlockPadRight
import CORALean.ContSet.PolyZonotope.Float.Operations.Stack
import CORALean.ContSet.PolyZonotope.Float.Operations.RmId
import CORALean.ContSet.PolyZonotope.Float.Operations.ReplaceId
import CORALean.ContSet.PolyZonotope.Float.Operations.OnlyId
import CORALean.ContSet.PolyZonotope.Float.Operations.RepresentsaPoint
import CORALean.ContSet.PolyZonotope.Float.Operations.SumErr
import CORALean.ContSet.PolyZonotope.Float.Operations.RepresentsaEmptySet
import CORALean.ContSet.PolyZonotope.Float.Operations.Sum
import CORALean.ContSet.PolyZonotope.Float.Operations.BoxOutRadius
import CORALean.ContSet.PolyZonotope.Float.Operations.BoxOut
import CORALean.ContSet.PolyZonotope.Float.Operations.OuterApprox
import CORALean.ContSet.PolyZonotope.Float.Operations.PartPatterns
import CORALean.ContSet.PolyZonotope.Float.Operations.PartZonotope
import CORALean.ContSet.PolyZonotope.Float.Operations.PolygonRound
import CORALean.ContSet.PolyZonotope.Float.Operations.PolygonPieces
import CORALean.ContSet.PolyZonotope.Float.Operations.Polygon
import CORALean.ContSet.PolyZonotope.Float.Operations.JacobianGap
import CORALean.ContSet.PolyZonotope.Float.Operations.Jacobian
import CORALean.ContSet.PolyZonotope.Float.Operations.SplitParallelotope
import CORALean.ContSet.PolyZonotope.Float.Operations.Split
import CORALean.ContSet.PolyZonotope.Float.Operations.IsFullDim
import CORALean.ContSet.PolyZonotope.Float.Operations.IsFullDimWith
import CORALean.ContSet.PolyZonotope.Float.Operations.ConvHull
import CORALean.ContSet.PolyZonotope.Float.Operations.MonoBox
import CORALean.ContSet.PolyZonotope.Float.Operations.PointBox
import CORALean.ContSet.PolyZonotope.Float.Operations.JacobianBox
import CORALean.ContSet.PolyZonotope.Float.Operations.PrecondRegular
import CORALean.ContSet.PolyZonotope.Float.Operations.SliceBox
import CORALean.ContSet.PolyZonotope.Float.Operations.InnerStep
import CORALean.ContSet.PolyZonotope.Float.Operations.InnerTest
import CORALean.ContSet.PolyZonotope.Float.Operations.InnerColumns
import CORALean.ContSet.PolyZonotope.Float.Operations.InnerSpecial
import CORALean.ContSet.PolyZonotope.Float.Operations.InnerGeneral
import CORALean.ContSet.PolyZonotope.Float.Operations.InnerApproxImage
import CORALean.ContSet.PolyZonotope.Float.Operations.InnerApprox
import CORALean.ContSet.PolyZonotope.Float.Operations.ContainsPointApprox
import CORALean.ContSet.PolyZonotope.Float.Operations.IndepFactors
import CORALean.ContSet.PolyZonotope.Float.Operations.SplitIndepGen
import CORALean.ContSet.PolyZonotope.Float.Operations.SplitLongestGenAll
import CORALean.ContSet.PolyZonotope.Float.Operations.ContainsSetApprox
import CORALean.ContSet.PolyZonotope.Float.Operations.CubMapGDown
import CORALean.ContSet.PolyZonotope.Float.Operations.CubMapGUp
import CORALean.ContSet.PolyZonotope.Float.Operations.CubMapGDiff
import CORALean.ContSet.PolyZonotope.Float.Operations.CubMapDep
import CORALean.ContSet.PolyZonotope.Float.Operations.CubMap
import CORALean.ContSet.PolyZonotope.Float.Operations.SubsMul
import CORALean.ContSet.PolyZonotope.Float.Operations.SubsPow
import CORALean.ContSet.PolyZonotope.Float.Operations.SubsPoly
import CORALean.ContSet.PolyZonotope.Float.Operations.SubsXprod
import CORALean.ContSet.PolyZonotope.Float.Operations.SubsTerms
import CORALean.ContSet.PolyZonotope.Float.Operations.SubsFactor
import CORALean.ContSet.PolyZonotope.Float.Operations.SubsGDown
import CORALean.ContSet.PolyZonotope.Float.Operations.SubsGDiff
import CORALean.ContSet.PolyZonotope.Float.Operations.Subs
import CORALean.ContSet.PolyZonotope.Float.Operations.ExtGens
import CORALean.ContSet.PolyZonotope.Float.Operations.PairG
import CORALean.ContSet.PolyZonotope.Float.Operations.PairGI
import CORALean.ContSet.PolyZonotope.Float.Operations.MatGeneratorError
import CORALean.ContSet.PolyZonotope.Float.Operations.MatMap

/-!
# What `PolyZonotope` computes

`plus`, `exactPlus`, `linComb` and `mtimes` pay their rounding into the error box rather than
into new generators. `linComb` pays nothing on the dependent side: halving and negation are
exact, so all three dependent blocks are copies. `quadMap` cannot: a quadratic map is not
additive, so a box cannot travel through it beside the nominal part, and `dependent` empties
the box into generators first.

`mul` carries that past degree two, spending it on one rounded product per
generator entry; `evalPoly` chains `mul` and prices the chaining itself.

`reduce` and the `compact` it runs first both *run* where the exact layer only specifies:
ranking needs a decidable order and merging columns a decidable equality, which a machine
scalar has and ℝ has not. `compact` alone differs in cost, merging adding entries.

`relaxExp` charges two column sums to the box and nothing else: its width is a count, not a
scalar, so the two layers relax by the same amount. `relaxExpEven` charges a third for the
centre it shifts, and `relaxExpMid` charges the same three at a shift with no sign to case on;
`relaxExpMulti` charges the first two at a width summed over every factor, and `relaxExpGreedy`
sequences steps and rounds nothing of its own.

No operation touches the exponent matrix numerically: it holds naturals, every
operation on it is exact, and the nominal set's monomials are the exact layer's.
-/
