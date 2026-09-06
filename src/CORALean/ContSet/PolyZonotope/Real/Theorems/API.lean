import CORALean.ContSet.PolyZonotope.Real.Theorems.AbsMonomialLeOne
import CORALean.ContSet.PolyZonotope.Real.Theorems.ContinuousMonomial
import CORALean.ContSet.PolyZonotope.Real.Theorems.MonomialZero
import CORALean.ContSet.PolyZonotope.Real.Theorems.MonomialAdd
import CORALean.ContSet.PolyZonotope.Real.Theorems.MemConstruct
import CORALean.ContSet.PolyZonotope.Real.Theorems.PointMemConstruct
import CORALean.ContSet.PolyZonotope.Real.Theorems.ExistsPointOfQZero
import CORALean.ContSet.PolyZonotope.Real.Theorems.MonomialPlusELeft
import CORALean.ContSet.PolyZonotope.Real.Theorems.MonomialPlusERight
import CORALean.ContSet.PolyZonotope.Real.Theorems.PlusExact
import CORALean.ContSet.PolyZonotope.Real.Theorems.MapExact
import CORALean.ContSet.PolyZonotope.Real.Theorems.MtimesExact
import CORALean.ContSet.PolyZonotope.Real.Theorems.MonomialLinCombEFst
import CORALean.ContSet.PolyZonotope.Real.Theorems.MonomialLinCombESnd
import CORALean.ContSet.PolyZonotope.Real.Theorems.MonomialLinCombELast
import CORALean.ContSet.PolyZonotope.Real.Theorems.LinCombOuter
import CORALean.ContSet.PolyZonotope.Real.Theorems.DependentExact
import CORALean.ContSet.PolyZonotope.Real.Theorems.SumExtEqPoint
import CORALean.ContSet.PolyZonotope.Real.Theorems.QuadEvalSumExt
import CORALean.ContSet.PolyZonotope.Real.Theorems.QuadMapDepExact
import CORALean.ContSet.PolyZonotope.Real.Theorems.QuadMapExact
import CORALean.ContSet.PolyZonotope.Real.Theorems.BilinPoint
import CORALean.ContSet.PolyZonotope.Real.Theorems.BilinExact
import CORALean.ContSet.PolyZonotope.Real.Theorems.PadBackPoint
import CORALean.ContSet.PolyZonotope.Real.Theorems.PadFrontPoint
import CORALean.ContSet.PolyZonotope.Real.Theorems.MulPoint
import CORALean.ContSet.PolyZonotope.Real.Theorems.MulExact
import CORALean.ContSet.PolyZonotope.Real.Theorems.EvalPolyReal
import CORALean.ContSet.PolyZonotope.Real.Theorems.EvalPolyStepPoint
import CORALean.ContSet.PolyZonotope.Real.Theorems.EvalPolyExact
import CORALean.ContSet.PolyZonotope.Real.Theorems.EvalPolyQ
import CORALean.ContSet.PolyZonotope.Real.Theorems.EvalPolyRealOfFn
import CORALean.ContSet.PolyZonotope.Real.Theorems.CompactGensExact
import CORALean.ContSet.PolyZonotope.Real.Theorems.CompactFactorsExact
import CORALean.ContSet.PolyZonotope.Real.Theorems.CompactExact
import CORALean.ContSet.PolyZonotope.Real.Theorems.ReduceByOuter
import CORALean.ContSet.PolyZonotope.Real.Theorems.ReduceGirardOuter
import CORALean.ContSet.PolyZonotope.Real.Theorems.ReduceGirardDependentOuter
import CORALean.ContSet.PolyZonotope.Real.Theorems.ReduceDependentOuter
import CORALean.ContSet.PolyZonotope.Real.Theorems.ReduceOuter
import CORALean.ContSet.PolyZonotope.Real.Theorems.ReduceGirardOrderLe
import CORALean.ContSet.PolyZonotope.Real.Theorems.ReduceOrder
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
import CORALean.ContSet.PolyZonotope.Real.Theorems.RelaxExpMidOuter
import CORALean.ContSet.PolyZonotope.Real.Theorems.ExpEdgeAcyclic
import CORALean.ContSet.PolyZonotope.Real.Theorems.RelaxExpEvenOuterOfEdge
import CORALean.ContSet.PolyZonotope.Real.Theorems.RelaxExpGreedyOuter

/-!
# What `PolyZonotope` guarantees

`plus`, `map`, `dependent`, `quadMap` and `compact` exactly; `linComb` and `reduce` as enclosures,
each docstring saying which coefficients or dropped generators cost the other way. `reduce` is the
one operation with two guarantees, and it needs both: an enclosure alone is met by a set that
grows every step, so `reduce_order_le` bounds the size it keeps.

`bilin_exact` equates a pairing with the image of the shared factors under `a ↦ f (point S₁ a)
(point S₂ a)`, never `f` over the two sets; `mul_exact` is it entrywise, `evalPoly_exact` carries
that to a polynomial per coordinate and `evalPolyReal_ofFn` matches Horner to the monomial sum.
`padBack_point` and `padFront_point` say padding moves no point, so *independent* factors pair by
`bilin` too. `point_mem_construct` is the way back and `exists_point_of_q_zero`, once `evalPoly_q`
says nothing is independent, the way there. `relaxExp_outer` holds at every partition naming two
generators, `eDiff` owing no optimality. `relaxExpEven_outer` adds evenness, `relaxExpMulti_outer`
asks nothing, and `sub_monomial_mem_eDrift` brackets the drift out of `sub_pow_nonpos` and
`sub_monomial_nonpos_of_pow`, letting `relaxExpMid_outer` shift at any parity. `expEdge_acyclic`
has no cycles, `relaxExpEven_outer_of_edge` reads an edge, and `relaxExpGreedy_outer` loops at any
selection.

`quadMap_exact` distinguishes the representation: no convex one here can state it. `compact_exact`
is what an order bound rests on: the generator count may fall without the set moving, which is
what `reduce_outer` trades against precision. The monomial facts and `MemConstruct` are what every
one of them is stated over.
-/
