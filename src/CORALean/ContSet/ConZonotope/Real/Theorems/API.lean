import CORALean.ContSet.ConZonotope.Real.Theorems.MemConstruct
import CORALean.ContSet.ConZonotope.Real.Theorems.ConstructEqImage
import CORALean.ContSet.ConZonotope.Real.Theorems.PlusExact
import CORALean.ContSet.ConZonotope.Real.Theorems.IntersectionExact
import CORALean.ContSet.ConZonotope.Real.Theorems.MapExact
import CORALean.ContSet.ConZonotope.Real.Theorems.MtimesExact
import CORALean.ContSet.ConZonotope.Real.Theorems.MtimesIntervalMatOuter
import CORALean.ContSet.ConZonotope.Real.Theorems.AbsSmulCoeffLeOne
import CORALean.ContSet.ConZonotope.Real.Theorems.SumUnivLinComb
import CORALean.ContSet.ConZonotope.Real.Theorems.LinCombOuter
import CORALean.ContSet.ConZonotope.Real.Theorems.LinCombInner
import CORALean.ContSet.ConZonotope.Real.Theorems.ReduceOuter
import CORALean.ContSet.ConZonotope.Real.Theorems.ReduceOrder
import CORALean.ContSet.ConZonotope.Real.Theorems.EncloseOuter
import CORALean.ContSet.ConZonotope.Real.Theorems.Convex
import CORALean.ContSet.ConZonotope.Real.Theorems.IsCompactDomain
import CORALean.ContSet.ConZonotope.Real.Theorems.IsCompact
import CORALean.ContSet.ConZonotope.Real.Theorems.IsClosed
import CORALean.ContSet.ConZonotope.Real.Theorems.IsBounded
import CORALean.ContSet.ConZonotope.Real.Theorems.OfPointMem
import CORALean.ContSet.ConZonotope.Real.Theorems.IsAffineImageIff
import CORALean.ContSet.ConZonotope.Real.Theorems.IntersectsHyperplaneIff

/-!
# What `ConZonotope` guarantees

`intersection`, `plus` and `map` exactly; the interval-matrix product and `reduce` as
enclosures, `reduce` by way of `zonotope_contains`, and `reduce_order_le` for its
own generator-count bound. `linComb` has both directions: `_outer` is what the
interface asks for and holds always, `_inner` is what says the result is the
convex hull itself and asks both sets to be nonempty. `enclose_outer` is the
one direction `enclose` gets, asking the constraints to agree besides. The
topological facts go through `ConstructEqImage` and so through the polytope,
which is where they differ from a zonotope's.

`OfPointMem` needs no theorem of `HPolytope`'s: an empty row index discharges
the constraint the same way it discharges the generator sum.

`IsAffineImageIff` is the representation itself characterized: exactly the
bounded affine images of a polytope, `ConstructEqImage` and `HPolytope`'s own
conversion read as the two halves of one iff. `IntersectsHyperplaneIff` reads
`convex_construct` as a hyperplane test, exact between the extremes `h` takes.

Together these are everything `LinearSys` reachability asks of a representation.
-/
