import CORALean.ContSet.ConZonotope.Real.Theorems.MemConstruct
import CORALean.ContSet.ConZonotope.Real.Theorems.ConstructEqImage
import CORALean.ContSet.ConZonotope.Real.Theorems.PlusExact
import CORALean.ContSet.ConZonotope.Real.Theorems.AndExact
import CORALean.ContSet.ConZonotope.Real.Theorems.MapExact
import CORALean.ContSet.ConZonotope.Real.Theorems.MtimesExact
import CORALean.ContSet.ConZonotope.Real.Theorems.MtimesIntervalMatOuter
import CORALean.ContSet.ConZonotope.Real.Theorems.LinCombOuter
import CORALean.ContSet.ConZonotope.Real.Theorems.ReduceOuter
import CORALean.ContSet.ConZonotope.Real.Theorems.Convex
import CORALean.ContSet.ConZonotope.Real.Theorems.IsCompactDomain
import CORALean.ContSet.ConZonotope.Real.Theorems.IsCompact
import CORALean.ContSet.ConZonotope.Real.Theorems.IsClosed
import CORALean.ContSet.ConZonotope.Real.Theorems.IsBounded

/-!
# What `ConZonotope` guarantees

`and`, `plus` and `map` exactly; the interval-matrix product, `linComb` and
`reduce` as enclosures — the last two by way of `zonotope_outer`. The
topological facts go through `ConstructEqImage` and so through the polytope,
which is where they differ from a zonotope's.

Together these are everything `LinearSys` reachability asks of a representation.
-/
