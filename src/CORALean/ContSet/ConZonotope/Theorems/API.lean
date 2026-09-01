import CORALean.ContSet.ConZonotope.Theorems.ZonotopeOuter
import CORALean.ContSet.ConZonotope.Theorems.PlusExact
import CORALean.ContSet.ConZonotope.Theorems.AndExact
import CORALean.ContSet.ConZonotope.Theorems.MapExact
import CORALean.ContSet.ConZonotope.Theorems.MtimesIntervalMatOuter
import CORALean.ContSet.ConZonotope.Theorems.LinCombOuter
import CORALean.ContSet.ConZonotope.Theorems.ReduceOuter
import CORALean.ContSet.ConZonotope.Theorems.Convex
import CORALean.ContSet.ConZonotope.Theorems.IsCompact

/-!
# What `ConZonotope` guarantees

`and`, `plus` and `map` exactly; the interval-matrix product, `linComb` and
`reduce` as enclosures — the last two by way of `zonotope_outer`. The
topological facts go through `domain` and so through the polytope, which is
where they differ from a zonotope's.

Together these are everything `LinearSys` reachability asks of a representation.
-/
