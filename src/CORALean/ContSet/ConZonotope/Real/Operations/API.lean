import CORALean.ContSet.ConZonotope.Real.Operations.OfMat
import CORALean.ContSet.ConZonotope.Real.Operations.MemOfMatIff
import CORALean.ContSet.ConZonotope.Real.Operations.Domain
import CORALean.ContSet.ConZonotope.Real.Operations.MemDomainIff
import CORALean.ContSet.ConZonotope.Real.Operations.Plus
import CORALean.ContSet.ConZonotope.Real.Operations.AgreeMat
import CORALean.ContSet.ConZonotope.Real.Operations.Intersection
import CORALean.ContSet.ConZonotope.Real.Operations.Map
import CORALean.ContSet.ConZonotope.Real.Operations.Mtimes
import CORALean.ContSet.ConZonotope.Real.Operations.MtimesEqMap
import CORALean.ContSet.ConZonotope.Real.Operations.MtimesIntervalMat
import CORALean.ContSet.ConZonotope.Real.Operations.LinComb
import CORALean.ContSet.ConZonotope.Real.Operations.Reduce
import CORALean.ContSet.ConZonotope.Real.Operations.OfPoint
import CORALean.ContSet.ConZonotope.Real.Operations.Enclose
import CORALean.ContSet.ConZonotope.Real.Operations.MinkDiffV

/-!
# What `ConZonotope` computes

`intersection`, `plus`, `map` and `mtimes` keep the constraints and stay exact — `intersection`
being the one a zonotope cannot have. Multiplication by an interval matrix keeps them too, and is
outer for the zonotope's reason rather than for the constraints'. `linComb` keeps them as well,
weighting each side's constraints by the interpolation parameter; between two nonempty sets it is
the convex hull exactly, where the enclosing zonotope is only an enclosure of it.

`enclose` keeps them too, for the aligned pair `linComb` also covers, at the same generator count
— what it buys over `linComb` is a far smaller constraint system, one copy of `cZ₁.P`'s own rows
rather than a halfScaled intersection of both sides'. The price is precision: `enclose` is only
outer, where `linComb` is exact between nonempty sets. Neither replaces the other.

`reduce` is the one operation that still goes through the enclosing zonotope and gives the
constraints up. CORA reduces the zonotope the constraint rows lift to and reads the rows back off
it, which asks for the equality system CORA's constraints are and this representation's polytope
need not be.

`OfMat` is CORA's constructor, whose constraints are an equality system, `Domain` is the
coefficient polytope the unit box and `P` make together, and `OfPoint` is the centre alone, at
`HPolytope.fullspace`. `MinkDiffV` folds `intersection` over a zonotope translated by each of a
polytope's vertices — Wetzlinger et al.'s Prop. 6, exact where every other difference here encloses.
-/
