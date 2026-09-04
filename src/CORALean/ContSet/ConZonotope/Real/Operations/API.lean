import CORALean.ContSet.ConZonotope.Real.Operations.OfMat
import CORALean.ContSet.ConZonotope.Real.Operations.Domain
import CORALean.ContSet.ConZonotope.Real.Operations.Plus
import CORALean.ContSet.ConZonotope.Real.Operations.And
import CORALean.ContSet.ConZonotope.Real.Operations.Map
import CORALean.ContSet.ConZonotope.Real.Operations.Mtimes
import CORALean.ContSet.ConZonotope.Real.Operations.MtimesIntervalMat
import CORALean.ContSet.ConZonotope.Real.Operations.LinComb
import CORALean.ContSet.ConZonotope.Real.Operations.Reduce

/-!
# What `ConZonotope` computes

`and`, `plus`, `map` and `mtimes` keep the constraints and stay exact — `and`
being the one a zonotope cannot have. Multiplication by an interval matrix keeps
them too, and is outer for the zonotope's reason rather than for the
constraints'. `linComb` and `reduce` go through the enclosing zonotope and give
the constraints up, which is where the representation currently loses precision
that CORA does not.

`OfMat` is CORA's constructor, whose constraints are an equality system, and
`Domain` is the coefficient polytope the unit box and `P` make together.
-/
