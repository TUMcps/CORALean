import CORALean.ContSet.PolyZonotope.Float.Theorems.MemNominalSet
import CORALean.ContSet.PolyZonotope.Float.Theorems.MemGeneratorError
import CORALean.ContSet.PolyZonotope.Float.Theorems.PlusOuter
import CORALean.ContSet.PolyZonotope.Float.Theorems.MtimesOuter
import CORALean.ContSet.PolyZonotope.Float.Theorems.CompactOuter
import CORALean.ContSet.PolyZonotope.Float.Theorems.DependentNominal
import CORALean.ContSet.PolyZonotope.Float.Theorems.LinCombOuter
import CORALean.ContSet.PolyZonotope.Float.Theorems.QuadMapOuter
import CORALean.ContSet.PolyZonotope.Float.Theorems.ReduceOuter
import CORALean.ContSet.PolyZonotope.Float.Theorems.ReduceOrder

/-!
# What `PolyZonotope` guarantees

The exact layer's `plus`, `linComb`, `map` and `quadMap` read as enclosures.
`plus`, `linComb` and `mtimes` keep the counts they have over ℝ, rounding going
into the error box;
`dependent_nominal` is the one that moves the other way, trading the box for
generators so that `quadMap` has a box-free set to work on.

`reduce_outer` holds at every pair of partitions, which is what lets the ranking
be a heuristic — and what lets it be computed at all here. It goes through
`compact_outer`, so the order `reduce_order_le` bounds is a count of distinct
monomials, as over ℝ; that bound is what keeps a reachability loop's
representation from growing a box per step.

`mem_generatorError` is the one that answers the question the representation
raises — what a monomial costs a float layer — and its docstring is where that
is argued. `MemNominalSet` is how each of them reads the nominal half of a point.
-/
