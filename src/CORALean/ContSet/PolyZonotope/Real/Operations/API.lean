import CORALean.ContSet.PolyZonotope.Real.Operations.IdentE
import CORALean.ContSet.PolyZonotope.Real.Operations.MonomialIdentE
import CORALean.ContSet.PolyZonotope.Real.Operations.Map
import CORALean.ContSet.PolyZonotope.Real.Operations.Mtimes
import CORALean.ContSet.PolyZonotope.Real.Operations.MtimesEqMap
import CORALean.ContSet.PolyZonotope.Real.Operations.PlusE
import CORALean.ContSet.PolyZonotope.Real.Operations.Plus
import CORALean.ContSet.PolyZonotope.Real.Operations.LinCombE
import CORALean.ContSet.PolyZonotope.Real.Operations.LinComb
import CORALean.ContSet.PolyZonotope.Real.Operations.Dependent
import CORALean.ContSet.PolyZonotope.Real.Operations.Point
import CORALean.ContSet.PolyZonotope.Real.Operations.ExtG
import CORALean.ContSet.PolyZonotope.Real.Operations.ExtE
import CORALean.ContSet.PolyZonotope.Real.Operations.ExtM
import CORALean.ContSet.PolyZonotope.Real.Operations.QuadEval
import CORALean.ContSet.PolyZonotope.Real.Operations.QuadMapG
import CORALean.ContSet.PolyZonotope.Real.Operations.QuadMapE
import CORALean.ContSet.PolyZonotope.Real.Operations.QuadMapDep
import CORALean.ContSet.PolyZonotope.Real.Operations.QuadMap
import CORALean.ContSet.PolyZonotope.Real.Operations.BilinE
import CORALean.ContSet.PolyZonotope.Real.Operations.BilinG
import CORALean.ContSet.PolyZonotope.Real.Operations.Bilin
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
import CORALean.ContSet.PolyZonotope.Real.Operations.DropRadius
import CORALean.ContSet.PolyZonotope.Real.Operations.ReduceBy
import CORALean.ContSet.PolyZonotope.Real.Operations.GirardMetric
import CORALean.ContSet.PolyZonotope.Real.Operations.GirardSplit
import CORALean.ContSet.PolyZonotope.Real.Operations.ReduceGirard
import CORALean.ContSet.PolyZonotope.Real.Operations.ReduceGirardDependent
import CORALean.ContSet.PolyZonotope.Real.Operations.Reduce
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
import CORALean.ContSet.PolyZonotope.Real.Operations.ExpEdgeAt
import CORALean.ContSet.PolyZonotope.Real.Operations.DecidableExpEdgeAt
import CORALean.ContSet.PolyZonotope.Real.Operations.ExpEdge
import CORALean.ContSet.PolyZonotope.Real.Operations.DecidableExpEdge
import CORALean.ContSet.PolyZonotope.Real.Operations.ExpGreedySel
import CORALean.ContSet.PolyZonotope.Real.Operations.RelaxExpGreedy

/-!
# What `PolyZonotope` computes

`plus`, `map` and `quadMap` exactly, `linComb` up to its independent block, and `dependent`, which
moves that block into the dependent one and is what lets `quadMap` be total.

`bilin` pairs two sets over shared factors by any bilinear map, exact against `point` and not the
two sets; `mul` is it entrywise, `quadMap` degree two this way, `evalPoly` any. `padBack` and
`padFront` widen a set's factors by another's at exponent zero, so *independent* factors reach it.

Each of those grows the generator counts, and `compact` brings them back down without changing the
set: equal exponent columns add, a zero generator goes, and so does a factor no column reads.
`reduce` then cuts the count to an order the caller names, and loses.

`relaxExp` merges two dependent generators whose exponent columns agree off one index, paying the
difference into one new independent generator at the price `eDiff` bounds. `relaxExpEven` halves
that price where the drift is one-sided, `relaxExpMulti` drops the agreement and sums `eDiff` over
every factor, and `eDrift` brackets the drift, which `relaxDrift` reads as the midpoint and
half-width `relaxExpMid` shifts and pays. `ExpEdgeAt` and `ExpEdge` graph the pairs worth merging;
`relaxExpGreedy` walks it at any selection.

`plusE`, `linCombE` and `quadMapE` are the exponent matrices the size-changing operations
assemble, each its own file (#62) since the float layer and `ConPolyZono` build on them too.
`identE` is the block `dependent` appends and a conversion's whole answer.
-/
