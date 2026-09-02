import CORALean.ContSet.PolyZonotope.Real.Theorems.PlusExact
import CORALean.ContSet.PolyZonotope.Real.Theorems.MapExact
import CORALean.ContSet.PolyZonotope.Real.Theorems.LinCombOuter
import CORALean.ContSet.PolyZonotope.Real.Theorems.DependentExact
import CORALean.ContSet.PolyZonotope.Real.Theorems.QuadMapExact
import CORALean.ContSet.PolyZonotope.Real.Theorems.CompactExact
import CORALean.ContSet.PolyZonotope.Real.Theorems.ReduceOuter

/-!
# What `PolyZonotope` guarantees

`plus`, `map`, `dependent`, `quadMap` and `compact` exactly; `linComb` and
`reduce` as enclosures, and the module docstring there says which coefficients,
respectively which dropped generators, cost the other direction.

`quadMap_exact` is the one that distinguishes the representation: no convex
representation here can state it. `compact_exact` is the one an order bound
rests on: it says the generator count may fall without the set moving, which is
what `reduce_outer` then trades against precision.
-/
