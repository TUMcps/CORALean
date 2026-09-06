import CORALean.ContSet.PolyZonotope.Float.Theorems.MemNominalSet
import CORALean.ContSet.PolyZonotope.Float.Theorems.MemGeneratorError
import CORALean.ContSet.PolyZonotope.Float.Theorems.MemGeneratorErrorMonomial
import CORALean.ContSet.PolyZonotope.Float.Theorems.PlusH
import CORALean.ContSet.PolyZonotope.Float.Theorems.PlusQ
import CORALean.ContSet.PolyZonotope.Float.Theorems.PlusOuter
import CORALean.ContSet.PolyZonotope.Float.Theorems.MtimesH
import CORALean.ContSet.PolyZonotope.Float.Theorems.MtimesQ
import CORALean.ContSet.PolyZonotope.Float.Theorems.MulVecSplit
import CORALean.ContSet.PolyZonotope.Float.Theorems.MatMulClose
import CORALean.ContSet.PolyZonotope.Float.Theorems.MtimesOuter
import CORALean.ContSet.PolyZonotope.Float.Theorems.RepIdem
import CORALean.ContSet.PolyZonotope.Float.Theorems.FiberEqZeroOfNotMem
import CORALean.ContSet.PolyZonotope.Float.Theorems.SumMask
import CORALean.ContSet.PolyZonotope.Float.Theorems.FiberDownLe
import CORALean.ContSet.PolyZonotope.Float.Theorems.LeFiberUp
import CORALean.ContSet.PolyZonotope.Float.Theorems.CompactGensOuter
import CORALean.ContSet.PolyZonotope.Float.Theorems.CompactFactorsNominal
import CORALean.ContSet.PolyZonotope.Float.Theorems.CompactFactorsOuter
import CORALean.ContSet.PolyZonotope.Float.Theorems.CompactOuter
import CORALean.ContSet.PolyZonotope.Float.Theorems.DependentQ
import CORALean.ContSet.PolyZonotope.Float.Theorems.ZeroMemDependentErr
import CORALean.ContSet.PolyZonotope.Float.Theorems.AbsLeErrorBound
import CORALean.ContSet.PolyZonotope.Float.Theorems.DependentNominal
import CORALean.ContSet.PolyZonotope.Float.Theorems.DependentOuter
import CORALean.ContSet.PolyZonotope.Float.Theorems.LinCombH
import CORALean.ContSet.PolyZonotope.Float.Theorems.LinCombQ
import CORALean.ContSet.PolyZonotope.Float.Theorems.LinCombOuter
import CORALean.ContSet.PolyZonotope.Float.Theorems.QuadDownLe
import CORALean.ContSet.PolyZonotope.Float.Theorems.LeQuadUp
import CORALean.ContSet.PolyZonotope.Float.Theorems.ToRealExtG
import CORALean.ContSet.PolyZonotope.Float.Theorems.QuadMapENominal
import CORALean.ContSet.PolyZonotope.Float.Theorems.QuadMapOuter
import CORALean.ContSet.PolyZonotope.Float.Theorems.MulGClose
import CORALean.ContSet.PolyZonotope.Float.Theorems.MulOuter
import CORALean.ContSet.PolyZonotope.Float.Theorems.EvalPolyOuter
import CORALean.ContSet.PolyZonotope.Float.Theorems.ReduceByH
import CORALean.ContSet.PolyZonotope.Float.Theorems.AbsDroppedLeDropRadius
import CORALean.ContSet.PolyZonotope.Float.Theorems.ReduceByOuter
import CORALean.ContSet.PolyZonotope.Float.Theorems.ReduceGirardOuter
import CORALean.ContSet.PolyZonotope.Float.Theorems.ReduceOuter
import CORALean.ContSet.PolyZonotope.Float.Theorems.ReduceGirardDependentOuter
import CORALean.ContSet.PolyZonotope.Float.Theorems.ReduceDependentOuter
import CORALean.ContSet.PolyZonotope.Float.Theorems.ReduceGirardOrderLe
import CORALean.ContSet.PolyZonotope.Float.Theorems.ReduceOrder
import CORALean.ContSet.PolyZonotope.Float.Theorems.RelaxExpOuter
import CORALean.ContSet.PolyZonotope.Float.Theorems.RelaxExpEvenOuter

/-!
# What `PolyZonotope` guarantees

The exact layer's `plus`, `linComb`, `map` and `quadMap` read as enclosures.
`plus`, `linComb` and `mtimes` keep the counts they have over ℝ, rounding going
into the error box; `dependent_nominal` moves the other way, trading the box for
generators so that `quadMap` has a box-free set to work on.

`mul_outer` encloses the exact product over shared factors, its input the two
*nominal* sets — reached by running `dependent` once. `evalPoly_outer` prices
the chain of `mul`s Horner runs, beyond what one `mul_outer` call owes.

`reduce_outer` holds at every pair of partitions, which is what lets the ranking be a heuristic
— and what lets it be computed at all here. It goes through `compact_outer`, so the order
`reduce_order_le` bounds is a count of distinct monomials, as over ℝ; that bound is what keeps
a reachability loop's representation from growing a box per step.

`relaxExp_outer` reads the exact layer's drift bound at the stored columns, the
two roundings it makes being the only difference between the layers, and
`relaxExpEven_outer` the same with a third for the centre it shifts.

`mem_generatorError` is the one that answers the question the representation
raises — what a monomial costs a float layer — and its docstring is where that
is argued. `MemNominalSet` is how each of them reads the nominal half of a point.
-/
