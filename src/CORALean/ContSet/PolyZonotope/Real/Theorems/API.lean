import CORALean.ContSet.PolyZonotope.Real.Theorems.AbsMonomialLeOne
import CORALean.ContSet.PolyZonotope.Real.Theorems.ContinuousMonomial
import CORALean.ContSet.PolyZonotope.Real.Theorems.MonomialZero
import CORALean.ContSet.PolyZonotope.Real.Theorems.MonomialAdd
import CORALean.ContSet.PolyZonotope.Real.Theorems.MemConstruct
import CORALean.ContSet.PolyZonotope.Real.Theorems.OfPointMem
import CORALean.ContSet.PolyZonotope.Real.Theorems.PointMemConstruct
import CORALean.ContSet.PolyZonotope.Real.Theorems.ExistsPointOfQZero
import CORALean.ContSet.PolyZonotope.Real.Theorems.SubsetAtMono
import CORALean.ContSet.PolyZonotope.Real.Theorems.SubsetAtSubsetConstruct
import CORALean.ContSet.PolyZonotope.Real.Theorems.SubsetAtUnitBox
import CORALean.ContSet.PolyZonotope.Real.Theorems.EvalOnUnitBox
import CORALean.ContSet.PolyZonotope.Real.Theorems.EvalOnMono
import CORALean.ContSet.PolyZonotope.Real.Theorems.GetSubsetPoint
import CORALean.ContSet.PolyZonotope.Real.Theorems.GetSubsetSubsetAt
import CORALean.ContSet.PolyZonotope.Real.Theorems.GetSubsetBox
import CORALean.ContSet.PolyZonotope.Real.Theorems.GetSubsetConstruct
import CORALean.ContSet.PolyZonotope.Real.Theorems.GetSubsetFixed
import CORALean.ContSet.PolyZonotope.Real.Theorems.GetSubsetEvalOn
import CORALean.ContSet.PolyZonotope.Real.Theorems.MonomialPlusELeft
import CORALean.ContSet.PolyZonotope.Real.Theorems.MonomialPlusERight
import CORALean.ContSet.PolyZonotope.Real.Theorems.PlusExact
import CORALean.ContSet.PolyZonotope.Real.Theorems.PlusMono
import CORALean.ContSet.PolyZonotope.Real.Theorems.PlusEvalOn
import CORALean.ContSet.PolyZonotope.Real.Theorems.ExactPlusPoint
import CORALean.ContSet.PolyZonotope.Real.Theorems.CartProdExact
import CORALean.ContSet.PolyZonotope.Real.Theorems.ExactCartProdPoint
import CORALean.ContSet.PolyZonotope.Real.Theorems.MapExact
import CORALean.ContSet.PolyZonotope.Real.Theorems.ProjectExact
import CORALean.ContSet.PolyZonotope.Real.Theorems.MapMono
import CORALean.ContSet.PolyZonotope.Real.Theorems.MapPoint
import CORALean.ContSet.PolyZonotope.Real.Theorems.MapSubsetAt
import CORALean.ContSet.PolyZonotope.Real.Theorems.MapEvalOn
import CORALean.ContSet.PolyZonotope.Real.Theorems.MtimesExact
import CORALean.ContSet.PolyZonotope.Real.Theorems.MtimesEvalOn
import CORALean.ContSet.PolyZonotope.Real.Theorems.MtimesIntervalMatOuter
import CORALean.ContSet.PolyZonotope.Real.Theorems.MonomialLinCombEFst
import CORALean.ContSet.PolyZonotope.Real.Theorems.MonomialLinCombESnd
import CORALean.ContSet.PolyZonotope.Real.Theorems.MonomialLinCombELast
import CORALean.ContSet.PolyZonotope.Real.Theorems.LinCombValue
import CORALean.ContSet.PolyZonotope.Real.Theorems.LinCombOuter
import CORALean.ContSet.PolyZonotope.Real.Theorems.LinCombValueDependent
import CORALean.ContSet.PolyZonotope.Real.Theorems.LinCombExactOfDependent
import CORALean.ContSet.PolyZonotope.Real.Theorems.DependentExact
import CORALean.ContSet.PolyZonotope.Real.Theorems.SumExtEqPoint
import CORALean.ContSet.PolyZonotope.Real.Theorems.QuadEvalSumExt
import CORALean.ContSet.PolyZonotope.Real.Theorems.QuadMapDepPoint
import CORALean.ContSet.PolyZonotope.Real.Theorems.QuadMapDepExact
import CORALean.ContSet.PolyZonotope.Real.Theorems.QuadMapExact
import CORALean.ContSet.PolyZonotope.Real.Theorems.BilinPoint
import CORALean.ContSet.PolyZonotope.Real.Theorems.BilinExact
import CORALean.ContSet.PolyZonotope.Real.Theorems.BilinSubsetAt
import CORALean.ContSet.PolyZonotope.Real.Theorems.BilinSubsetAtSubsetImage2
import CORALean.ContSet.PolyZonotope.Real.Theorems.QuadMapMixedExact
import CORALean.ContSet.PolyZonotope.Real.Theorems.PadBackPoint
import CORALean.ContSet.PolyZonotope.Real.Theorems.PadBackExact
import CORALean.ContSet.PolyZonotope.Real.Theorems.PadBackSubsetAt
import CORALean.ContSet.PolyZonotope.Real.Theorems.PadFrontPoint
import CORALean.ContSet.PolyZonotope.Real.Theorems.PadFrontSubsetAt
import CORALean.ContSet.PolyZonotope.Real.Theorems.MulPoint
import CORALean.ContSet.PolyZonotope.Real.Theorems.MulSubsetAt
import CORALean.ContSet.PolyZonotope.Real.Theorems.MulExact
import CORALean.ContSet.PolyZonotope.Real.Theorems.EvalPolyReal
import CORALean.ContSet.PolyZonotope.Real.Theorems.EvalPolyStepPoint
import CORALean.ContSet.PolyZonotope.Real.Theorems.EvalPolyExact
import CORALean.ContSet.PolyZonotope.Real.Theorems.EvalPolyQ
import CORALean.ContSet.PolyZonotope.Real.Theorems.EvalPolyRealOfFn
import CORALean.ContSet.PolyZonotope.Real.Theorems.CompactGensExact
import CORALean.ContSet.PolyZonotope.Real.Theorems.CompactFactorsExact
import CORALean.ContSet.PolyZonotope.Real.Theorems.CompactExact
import CORALean.ContSet.PolyZonotope.Real.Theorems.ReindexExact
import CORALean.ContSet.PolyZonotope.Real.Theorems.SortExact
import CORALean.ContSet.PolyZonotope.Real.Theorems.SortSorted
import CORALean.ContSet.PolyZonotope.Real.Theorems.MergeExact
import CORALean.ContSet.PolyZonotope.Real.Theorems.MergeSorted
import CORALean.ContSet.PolyZonotope.Real.Theorems.MergeColInjective
import CORALean.ContSet.PolyZonotope.Real.Theorems.SortPlusExact
import CORALean.ContSet.PolyZonotope.Real.Theorems.SortPlusSorted
import CORALean.ContSet.PolyZonotope.Real.Theorems.ReindexPoint
import CORALean.ContSet.PolyZonotope.Real.Theorems.SortPoint
import CORALean.ContSet.PolyZonotope.Real.Theorems.MergePoint
import CORALean.ContSet.PolyZonotope.Real.Theorems.SortPlusPoint
import CORALean.ContSet.PolyZonotope.Real.Theorems.ShiftPoint
import CORALean.ContSet.PolyZonotope.Real.Theorems.PowSortPoint
import CORALean.ContSet.PolyZonotope.Real.Theorems.EvalPolySortTailPoint
import CORALean.ContSet.PolyZonotope.Real.Theorems.EvalPolySortExact
import CORALean.ContSet.PolyZonotope.Real.Theorems.EvalPolySortSorted
import CORALean.ContSet.PolyZonotope.Real.Theorems.ReduceByOuter
import CORALean.ContSet.PolyZonotope.Real.Theorems.ReduceByEvalOn
import CORALean.ContSet.PolyZonotope.Real.Theorems.DropIndepStretchOuter
import CORALean.ContSet.PolyZonotope.Real.Theorems.ReduceGirardOuter
import CORALean.ContSet.PolyZonotope.Real.Theorems.ReduceGirardDependentOuter
import CORALean.ContSet.PolyZonotope.Real.Theorems.ReduceDependentOuter
import CORALean.ContSet.PolyZonotope.Real.Theorems.ReduceOuter
import CORALean.ContSet.PolyZonotope.Real.Theorems.ReduceEvalOn
import CORALean.ContSet.PolyZonotope.Real.Theorems.PostEvalOn
import CORALean.ContSet.PolyZonotope.Real.Theorems.ReduceGirardOrderLe
import CORALean.ContSet.PolyZonotope.Real.Theorems.ReduceOrder
import CORALean.ContSet.PolyZonotope.Real.Theorems.RestructureOuter
import CORALean.ContSet.PolyZonotope.Real.Theorems.RestructureQ
import CORALean.ContSet.PolyZonotope.Real.Theorems.RestructureP
import CORALean.ContSet.PolyZonotope.Real.Theorems.RestructureReduceOuter
import CORALean.ContSet.PolyZonotope.Real.Theorems.RestructureReduceOrder
import CORALean.ContSet.PolyZonotope.Real.Theorems.AbsSubPowLeEDiff
import CORALean.ContSet.PolyZonotope.Real.Theorems.AbsSubMonomialLe
import CORALean.ContSet.PolyZonotope.Real.Theorems.SubPowNonpos
import CORALean.ContSet.PolyZonotope.Real.Theorems.SubMonomialNonposOfPow
import CORALean.ContSet.PolyZonotope.Real.Theorems.SubMonomialNonpos
import CORALean.ContSet.PolyZonotope.Real.Theorems.SubMonomialMemEDrift
import CORALean.ContSet.PolyZonotope.Real.Theorems.RelaxExpOuter
import CORALean.ContSet.PolyZonotope.Real.Theorems.AbsSubMonomialLeSum
import CORALean.ContSet.PolyZonotope.Real.Theorems.RelaxExpEvenOuter
import CORALean.ContSet.PolyZonotope.Real.Theorems.RelaxExpMultiOuter
import CORALean.ContSet.PolyZonotope.Real.Theorems.RelaxExpGroupOuter
import CORALean.ContSet.PolyZonotope.Real.Theorems.RelaxWidthGroupLeChain
import CORALean.ContSet.PolyZonotope.Real.Theorems.RelaxExpGroupNotAlwaysTighter
import CORALean.ContSet.PolyZonotope.Real.Theorems.RelaxExpMidOuter
import CORALean.ContSet.PolyZonotope.Real.Theorems.ExpEdgeAcyclic
import CORALean.ContSet.PolyZonotope.Real.Theorems.RelaxExpEvenOuterOfEdge
import CORALean.ContSet.PolyZonotope.Real.Theorems.RelaxExpGreedyOuter

/-!
# What `PolyZonotope` guarantees

`plus`, `map`, `dependent`, `quadMap` and `compact` exactly; `linComb` and `reduce` as enclosures.
`reduce` is the one operation with two guarantees: an enclosure alone is met by a set that grows
every step, so `reduce_order_le` bounds the size it keeps. `map_point`/`map_subsetAt` are `map` at
one factor vector and at a sub-box, and `mtimesIntervalMat_outer` boxes the radius into a fresh
independent block. `mem_ofPoint` needs none of that guarding — there is nothing to bound.

`bilin_exact` equates a pairing with the image of the shared factors under `a ↦ f (point pZ₁ a)
(point pZ₂ a)`, never `f` over the two sets; `mul_exact` is it entrywise, `evalPoly_exact` carries
it to a polynomial per coordinate and `evalPolyReal_ofFn` matches Horner to the monomial sum.
`padBack_point`/`padFront_point` say padding moves no point, so *independent* factors pair too.
`point_mem_construct`/`subsetAt_subset_construct` are the way back, `exists_point_of_q_zero` and
`subsetAt_unitBox` the way there; `getSubset_construct` then represents a factor sub-box *exactly*.
`relaxExp_outer` holds at every partition naming two generators, `relaxExpEven_outer` adds evenness,
`relaxExpMulti_outer` asks nothing and `relaxExpGroup_outer` nothing of a whole group, priced by
`relaxWidthGroup_le_chain`. `sub_monomial_mem_eDrift` brackets the drift out of `sub_pow_nonpos` and
`sub_monomial_nonpos_of_pow`, letting `relaxExpMid_outer` shift at any parity. `expEdge_acyclic` has
no cycles, `relaxExpEven_outer_of_edge` reads an edge, `relaxExpGreedy_outer` at any selection.

`quadMap_exact` distinguishes the representation: no convex one here can state it. `compact_exact`
is what an order bound rests on: the generator count may fall without the set moving, which
`reduce_outer` trades against precision. The monomial facts and `MemConstruct` underlie all of it.
-/
