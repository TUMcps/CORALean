import CORALean.ContSet.PolyZonotope.Real.Theorems.AbsMonomialLeOne
import CORALean.ContSet.PolyZonotope.Real.Theorems.ContinuousMonomial
import CORALean.ContSet.PolyZonotope.Real.Theorems.MonomialZero
import CORALean.ContSet.PolyZonotope.Real.Theorems.MonomialAdd
import CORALean.ContSet.PolyZonotope.Real.Theorems.MemConstruct
import CORALean.ContSet.PolyZonotope.Real.Theorems.PointMemConstruct
import CORALean.ContSet.PolyZonotope.Real.Theorems.ExistsPointOfQZero
import CORALean.ContSet.PolyZonotope.Real.Theorems.PlusExact
import CORALean.ContSet.PolyZonotope.Real.Theorems.MapExact
import CORALean.ContSet.PolyZonotope.Real.Theorems.MtimesExact
import CORALean.ContSet.PolyZonotope.Real.Theorems.LinCombOuter
import CORALean.ContSet.PolyZonotope.Real.Theorems.DependentExact
import CORALean.ContSet.PolyZonotope.Real.Theorems.SumExtEqPoint
import CORALean.ContSet.PolyZonotope.Real.Theorems.QuadEvalSumExt
import CORALean.ContSet.PolyZonotope.Real.Theorems.QuadMapDepExact
import CORALean.ContSet.PolyZonotope.Real.Theorems.QuadMapExact
import CORALean.ContSet.PolyZonotope.Real.Theorems.MulExact
import CORALean.ContSet.PolyZonotope.Real.Theorems.EvalPolyExact
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
import CORALean.ContSet.PolyZonotope.Real.Theorems.RelaxExpOuter

/-!
# What `PolyZonotope` guarantees

`plus`, `map`, `dependent`, `quadMap` and `compact` exactly; `linComb` and
`reduce` as enclosures, and the module docstring there says which coefficients,
respectively which dropped generators, cost the other direction.

`reduce` is the one operation with two guarantees, and it needs both: an
enclosure alone is satisfied by a set that grows every step, so
`reduce_order_le` says the representation stays the size it was asked for.

`mul_exact` equates a product with the image of the shared factors under
`a ↦ point S₁ a ⊙ point S₂ a`, never with a product of the two sets;
`evalPoly_exact` carries that to a polynomial per coordinate.
`point_mem_construct` is the way back and `exists_point_of_q_zero` the way
there, once nothing is independent. `relaxExp_outer` holds at every partition
naming two generators, `eDiff` owing no proof of optimality: it bounds the
drift from above, and a sharper bound would only be more precise.

`quadMap_exact` is the one that distinguishes the representation: no convex
representation here can state it. `compact_exact` is the one an order bound
rests on: it says the generator count may fall without the set moving, which is
what `reduce_outer` then trades against precision. The monomial facts and
`MemConstruct` are what every one of them is stated over.
-/
