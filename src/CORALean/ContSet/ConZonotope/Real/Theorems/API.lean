import CORALean.ContSet.ConZonotope.Real.Theorems.MemConstruct
import CORALean.ContSet.ConZonotope.Real.Theorems.ConstructEqImage
import CORALean.ContSet.ConZonotope.Real.Theorems.PlusExact
import CORALean.ContSet.ConZonotope.Real.Theorems.AndExact
import CORALean.ContSet.ConZonotope.Real.Theorems.MapExact
import CORALean.ContSet.ConZonotope.Real.Theorems.MtimesExact
import CORALean.ContSet.ConZonotope.Real.Theorems.MtimesIntervalMatOuter
import CORALean.ContSet.ConZonotope.Real.Theorems.AbsSmulCoeffLeOne
import CORALean.ContSet.ConZonotope.Real.Theorems.SumUnivLinComb
import CORALean.ContSet.ConZonotope.Real.Theorems.LinCombOuter
import CORALean.ContSet.ConZonotope.Real.Theorems.LinCombInner
import CORALean.ContSet.ConZonotope.Real.Theorems.ReduceOuter
import CORALean.ContSet.ConZonotope.Real.Theorems.Convex
import CORALean.ContSet.ConZonotope.Real.Theorems.IsCompactDomain
import CORALean.ContSet.ConZonotope.Real.Theorems.IsCompact
import CORALean.ContSet.ConZonotope.Real.Theorems.IsClosed
import CORALean.ContSet.ConZonotope.Real.Theorems.IsBounded
import CORALean.ContSet.ConZonotope.Real.Theorems.OfPointMem

/-!
# What `ConZonotope` guarantees

`and`, `plus` and `map` exactly; the interval-matrix product and `reduce` as
enclosures, `reduce` by way of `zonotope_outer`. `linComb` has both directions:
`_outer` is what the interface asks for and holds always, `_inner` is what says
the result is the convex hull itself and asks both sets to be nonempty. The
topological facts go through `ConstructEqImage` and so through the polytope,
which is where they differ from a zonotope's.

`OfPointMem` needs no theorem of `HPolytope`'s: an empty row index discharges
the constraint the same way it discharges the generator sum.

Together these are everything `LinearSys` reachability asks of a representation.
-/
