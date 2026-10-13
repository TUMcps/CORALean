import CORALean.ContSet.PolyZonotope.Real.Operations.Isequal
import CORALean.ContSet.PolyZonotope.Real.Operations.IdentE
import CORALean.ContSet.PolyZonotope.Real.Operations.MonomialIdentE
import CORALean.ContSet.PolyZonotope.Real.Operations.Map
import CORALean.ContSet.PolyZonotope.Real.Operations.Project
import CORALean.ContSet.PolyZonotope.Real.Operations.Mtimes
import CORALean.ContSet.PolyZonotope.Real.Operations.MtimesEqMap
import CORALean.ContSet.PolyZonotope.Real.Operations.RadiusReach
import CORALean.ContSet.PolyZonotope.Real.Operations.MtimesIntervalMat
import CORALean.ContSet.PolyZonotope.Real.Operations.PlusE
import CORALean.ContSet.PolyZonotope.Real.Operations.Plus
import CORALean.ContSet.PolyZonotope.Real.Operations.ExactPlus
import CORALean.ContSet.PolyZonotope.Real.Operations.Stack
import CORALean.ContSet.PolyZonotope.Real.Operations.Resolve
import CORALean.ContSet.PolyZonotope.Real.Operations.CartProd
import CORALean.ContSet.PolyZonotope.Real.Operations.ExactCartProd
import CORALean.ContSet.PolyZonotope.Real.Operations.LinCombE
import CORALean.ContSet.PolyZonotope.Real.Operations.LinComb
import CORALean.ContSet.PolyZonotope.Real.Operations.Dependent
import CORALean.ContSet.PolyZonotope.Real.Operations.Point
import CORALean.ContSet.PolyZonotope.Real.Operations.NoIndep
import CORALean.ContSet.PolyZonotope.Real.Operations.OfPoint
import CORALean.ContSet.PolyZonotope.Real.Operations.SubsetAt
import CORALean.ContSet.PolyZonotope.Real.Operations.EvalOn
import CORALean.ContSet.PolyZonotope.Real.Operations.SupportBound
import CORALean.ContSet.PolyZonotope.Real.Operations.MaxExp
import CORALean.ContSet.PolyZonotope.Real.Operations.GetSubsetE
import CORALean.ContSet.PolyZonotope.Real.Operations.GetSubsetG
import CORALean.ContSet.PolyZonotope.Real.Operations.GetSubset
import CORALean.ContSet.PolyZonotope.Real.Operations.PlusBox
import CORALean.ContSet.PolyZonotope.Real.Operations.ExtG
import CORALean.ContSet.PolyZonotope.Real.Operations.ExtE
import CORALean.ContSet.PolyZonotope.Real.Operations.ExtM
import CORALean.ContSet.PolyZonotope.Real.Operations.QuadEval
import CORALean.ContSet.PolyZonotope.Real.Operations.QuadBilin
import CORALean.ContSet.PolyZonotope.Real.Operations.QuadMapG
import CORALean.ContSet.PolyZonotope.Real.Operations.QuadMapE
import CORALean.ContSet.PolyZonotope.Real.Operations.QuadMapDep
import CORALean.ContSet.PolyZonotope.Real.Operations.QuadMap
import CORALean.ContSet.PolyZonotope.Real.Operations.BilinE
import CORALean.ContSet.PolyZonotope.Real.Operations.BilinG
import CORALean.ContSet.PolyZonotope.Real.Operations.Bilin
import CORALean.ContSet.PolyZonotope.Real.Operations.BilinGI
import CORALean.ContSet.PolyZonotope.Real.Operations.BilinOuter
import CORALean.ContSet.PolyZonotope.Real.Operations.MatMap
import CORALean.ContSet.PolyZonotope.Real.Operations.QuadMapMixed
import CORALean.ContSet.PolyZonotope.Real.Operations.PadE
import CORALean.ContSet.PolyZonotope.Real.Operations.PadFrontE
import CORALean.ContSet.PolyZonotope.Real.Operations.PadBack
import CORALean.ContSet.PolyZonotope.Real.Operations.PadFront
import CORALean.ContSet.PolyZonotope.Real.Operations.MulG
import CORALean.ContSet.PolyZonotope.Real.Operations.MulE
import CORALean.ContSet.PolyZonotope.Real.Operations.MulGApply
import CORALean.ContSet.PolyZonotope.Real.Operations.Mul
import CORALean.ContSet.PolyZonotope.Real.Operations.EvalPolyStep
import CORALean.ContSet.PolyZonotope.Real.Operations.EvalPolyP
import CORALean.ContSet.PolyZonotope.Real.Operations.EvalPoly
import CORALean.ContSet.PolyZonotope.Real.Operations.EvalPolyFactorCount
import CORALean.ContSet.PolyZonotope.Real.Operations.Col
import CORALean.ContSet.PolyZonotope.Real.Operations.FiberSum
import CORALean.ContSet.PolyZonotope.Real.Operations.SumMonomialMerge
import CORALean.ContSet.PolyZonotope.Real.Operations.Rep
import CORALean.ContSet.PolyZonotope.Real.Operations.ColRep
import CORALean.ContSet.PolyZonotope.Real.Operations.CompactKeep
import CORALean.ContSet.PolyZonotope.Real.Operations.FiberSumEqZeroOfNotMem
import CORALean.ContSet.PolyZonotope.Real.Operations.CompactIdx
import CORALean.ContSet.PolyZonotope.Real.Operations.SumCompactKeep
import CORALean.ContSet.PolyZonotope.Real.Operations.CompactGens
import CORALean.ContSet.PolyZonotope.Real.Operations.UsedFactors
import CORALean.ContSet.PolyZonotope.Real.Operations.FactorIdx
import CORALean.ContSet.PolyZonotope.Real.Operations.FactorExtend
import CORALean.ContSet.PolyZonotope.Real.Operations.AbsFactorExtendLeOne
import CORALean.ContSet.PolyZonotope.Real.Operations.FactorExtendFactorIdx
import CORALean.ContSet.PolyZonotope.Real.Operations.MonomialFactorIdx
import CORALean.ContSet.PolyZonotope.Real.Operations.MonomialFactorExtend
import CORALean.ContSet.PolyZonotope.Real.Operations.CompactFactors
import CORALean.ContSet.PolyZonotope.Real.Operations.Compact
import CORALean.ContSet.PolyZonotope.Real.Operations.RepCongr
import CORALean.ContSet.PolyZonotope.Real.Operations.MergeKeep
import CORALean.ContSet.PolyZonotope.Real.Operations.MergeIdx
import CORALean.ContSet.PolyZonotope.Real.Operations.SumMergeKeep
import CORALean.ContSet.PolyZonotope.Real.Operations.FiberSumEqZeroOfNotMemMerge
import CORALean.ContSet.PolyZonotope.Real.Operations.Merge
import CORALean.ContSet.PolyZonotope.Real.Operations.Reindex
import CORALean.ContSet.PolyZonotope.Real.Operations.ColLex
import CORALean.ContSet.PolyZonotope.Real.Operations.Sorted
import CORALean.ContSet.PolyZonotope.Real.Operations.SortPerm
import CORALean.ContSet.PolyZonotope.Real.Operations.Sort
import CORALean.ContSet.PolyZonotope.Real.Operations.SortPlus
import CORALean.ContSet.PolyZonotope.Real.Operations.Shift
import CORALean.ContSet.PolyZonotope.Real.Operations.PowSort
import CORALean.ContSet.PolyZonotope.Real.Operations.EvalPolySortTailP
import CORALean.ContSet.PolyZonotope.Real.Operations.EvalPolySortP
import CORALean.ContSet.PolyZonotope.Real.Operations.EvalPolySort
import CORALean.ContSet.PolyZonotope.Real.Operations.EvalPolySortFactorCount
import CORALean.ContSet.PolyZonotope.Real.Operations.DropRadius
import CORALean.ContSet.PolyZonotope.Real.Operations.DropIndepMat
import CORALean.ContSet.PolyZonotope.Real.Operations.DropIndepStretch
import CORALean.ContSet.PolyZonotope.Real.Operations.ReduceBy
import CORALean.ContSet.PolyZonotope.Real.Operations.GirardMetric
import CORALean.ContSet.PolyZonotope.Real.Operations.GirardSplit
import CORALean.ContSet.PolyZonotope.Real.Operations.ReduceGirard
import CORALean.ContSet.PolyZonotope.Real.Operations.ReduceGirardDependent
import CORALean.ContSet.PolyZonotope.Real.Operations.Reduce
import CORALean.ContSet.PolyZonotope.Real.Operations.ReduceBox
import CORALean.ContSet.PolyZonotope.Real.Operations.PostBox
import CORALean.ContSet.PolyZonotope.Real.Operations.Restructure
import CORALean.ContSet.PolyZonotope.Real.Operations.RestructureReduce
import CORALean.ContSet.PolyZonotope.Real.Operations.ReduceDependent
import CORALean.ContSet.PolyZonotope.Real.Operations.EDiff
import CORALean.ContSet.PolyZonotope.Real.Operations.EDrift
import CORALean.ContSet.PolyZonotope.Real.Operations.RelaxWidth
import CORALean.ContSet.PolyZonotope.Real.Operations.RelaxExp
import CORALean.ContSet.PolyZonotope.Real.Operations.RelaxExpEven
import CORALean.ContSet.PolyZonotope.Real.Operations.RelaxDrift
import CORALean.ContSet.PolyZonotope.Real.Operations.RelaxExpMid
import CORALean.ContSet.PolyZonotope.Real.Operations.RelaxWidthMulti
import CORALean.ContSet.PolyZonotope.Real.Operations.RelaxExpMulti
import CORALean.ContSet.PolyZonotope.Real.Operations.RelaxWidthGroup
import CORALean.ContSet.PolyZonotope.Real.Operations.RelaxExpGroup
import CORALean.ContSet.PolyZonotope.Real.Operations.ExpEdgeAt
import CORALean.ContSet.PolyZonotope.Real.Operations.DecidableExpEdgeAt
import CORALean.ContSet.PolyZonotope.Real.Operations.ExpEdge
import CORALean.ContSet.PolyZonotope.Real.Operations.DecidableExpEdge
import CORALean.ContSet.PolyZonotope.Real.Operations.ExpGreedySel
import CORALean.ContSet.PolyZonotope.Real.Operations.RelaxExpGreedy
import CORALean.ContSet.PolyZonotope.Real.Operations.IsFullDimCora
import CORALean.ContSet.PolyZonotope.Real.Operations.LongestFactor
import CORALean.ContSet.PolyZonotope.Real.Operations.RmId
import CORALean.ContSet.PolyZonotope.Real.Operations.SplitDepFactor
import CORALean.ContSet.PolyZonotope.Real.Operations.SplitLongestGen
import CORALean.ContSet.PolyZonotope.Real.Operations.SplitParallelotope
import CORALean.ContSet.PolyZonotope.Real.Operations.Split
import CORALean.ContSet.PolyZonotope.Real.Operations.SplitAll
import CORALean.ContSet.PolyZonotope.Real.Operations.BoxOut
import CORALean.ContSet.PolyZonotope.Real.Operations.OuterApprox
import CORALean.ContSet.PolyZonotope.Real.Operations.PartPattern
import CORALean.ContSet.PolyZonotope.Real.Operations.PartPatterns
import CORALean.ContSet.PolyZonotope.Real.Operations.PartZonotope
import CORALean.ContSet.PolyZonotope.Real.Operations.SubsMul
import CORALean.ContSet.PolyZonotope.Real.Operations.SubsPow
import CORALean.ContSet.PolyZonotope.Real.Operations.SubsPoly
import CORALean.ContSet.PolyZonotope.Real.Operations.SubsXprod
import CORALean.ContSet.PolyZonotope.Real.Operations.SubsTerms
import CORALean.ContSet.PolyZonotope.Real.Operations.SubsFactor
import CORALean.ContSet.PolyZonotope.Real.Operations.Subs
import CORALean.ContSet.PolyZonotope.Real.Operations.Sum
import CORALean.ContSet.PolyZonotope.Real.Operations.SumCora
import CORALean.ContSet.PolyZonotope.Real.Operations.RepresentsaPoint
import CORALean.ContSet.PolyZonotope.Real.Operations.RepresentsaEmptySet
import CORALean.ContSet.PolyZonotope.Real.Operations.ReplaceId
import CORALean.ContSet.PolyZonotope.Real.Operations.OnlyId
import CORALean.ContSet.PolyZonotope.Real.Operations.Jacobian
import CORALean.ContSet.PolyZonotope.Real.Operations.ZonotopeCora
import CORALean.ContSet.PolyZonotope.Real.Operations.SplitLongestIndepGen
import CORALean.ContSet.PolyZonotope.Real.Operations.ContainsPointSet
import CORALean.ContSet.PolyZonotope.Real.Operations.ContainsExactCora1D
import CORALean.ContSet.PolyZonotope.Real.Operations.Volume
import CORALean.ContSet.PolyZonotope.Real.Operations.AddedTerms
import CORALean.ContSet.PolyZonotope.Real.Operations.Polygon
import CORALean.ContSet.PolyZonotope.Real.Operations.CoraWeight
import CORALean.ContSet.PolyZonotope.Real.Operations.SplitGen
import CORALean.ContSet.PolyZonotope.Real.Operations.SplitMany
import CORALean.ContSet.PolyZonotope.Real.Operations.PolygonRound
import CORALean.ContSet.PolyZonotope.Real.Operations.PolygonPieces
import CORALean.ContSet.PolyZonotope.Real.Operations.JacobianMat
import CORALean.ContSet.PolyZonotope.Real.Operations.JacobianDetIntegral
import CORALean.ContSet.PolyZonotope.Real.Operations.AddedTermsHessian
import CORALean.ContSet.PolyZonotope.Real.Operations.CubEval
import CORALean.ContSet.PolyZonotope.Real.Operations.CubEvalMixed
import CORALean.ContSet.PolyZonotope.Real.Operations.CubPair
import CORALean.ContSet.PolyZonotope.Real.Operations.CubQuad
import CORALean.ContSet.PolyZonotope.Real.Operations.CubMapDep
import CORALean.ContSet.PolyZonotope.Real.Operations.CubMapDepSingle
import CORALean.ContSet.PolyZonotope.Real.Operations.CubMap
import CORALean.ContSet.PolyZonotope.Real.Operations.CubMapMixed
import CORALean.ContSet.PolyZonotope.Real.Operations.SquareExample
import CORALean.ContSet.PolyZonotope.Real.Operations.IsPolytopeCex
import CORALean.ContSet.PolyZonotope.Real.Operations.IsPolytopeCexCorners
import CORALean.ContSet.PolyZonotope.Real.Operations.CoraVertex
import CORALean.ContSet.PolyZonotope.Real.Operations.CoraNormalCone
import CORALean.ContSet.PolyZonotope.Real.Operations.InCone
import CORALean.ContSet.PolyZonotope.Real.Operations.CoraAccepts
import CORALean.ContSet.PolyZonotope.Real.Operations.ConvHull
import CORALean.ContSet.PolyZonotope.Real.Operations.ExpWeight
import CORALean.ContSet.PolyZonotope.Real.Operations.PairSplit
import CORALean.ContSet.PolyZonotope.Real.Operations.GreedyTarget
import CORALean.ContSet.PolyZonotope.Real.Operations.LeafNode
import CORALean.ContSet.PolyZonotope.Real.Operations.RelaxGreedy
import CORALean.ContSet.PolyZonotope.Real.Operations.InnerScaling

/-!
# What `PolyZonotope` computes

`plus`, `map` and `quadMap` exactly, `linComb` up to its independent block, and `dependent`, which
moves that block into the dependent one and is what lets `quadMap` be total. `mtimesIntervalMat`
boxes an interval matrix's radius into fresh independent generators, priced by `radiusReach`.

`bilin` pairs two sets over shared factors by any bilinear map, exact against `point`; `mul` is it
at `hadamardLin`, `quadMap` at `quadBilin`, `evalPoly` any degree. `padBack` and `padFront` widen by
another set's factors at exponent zero, so *independent* factors reach it. `subsetAt` names what a
factor sub-box reaches; `getSubset` represents it, `getSubsetG` at `getSubsetE`, sized by `maxExp`.

Each of those grows the generator counts, and `compact` brings them back down without changing the
set: equal exponent columns add, a zero generator goes, and so does a factor no column reads.
`reduce` then cuts the count to an order the caller names, and loses; `ofPoint` needs none of it.

`relaxExp` merges two dependent generators whose columns agree off one index, paying the difference
into a new independent generator, priced by `eDiff`; `eDrift` brackets that drift, read at the
midpoint by `relaxDrift`/`relaxExpMid`. `relaxExpEven` halves the price at a one-sided drift,
`relaxExpMulti` drops the agreement, summing over every factor, and `relaxExpGroup` merges a whole
group at once; `ExpEdgeAt`/`ExpEdge` graph the pairs, `relaxExpGreedy` walking it at any pick.

`plusE`, `linCombE` and `quadMapE` are the exponent matrices the size-changing operations assemble,
each its own file (#62); `identE` is the block `dependent` appends and a conversion's whole answer.
-/
