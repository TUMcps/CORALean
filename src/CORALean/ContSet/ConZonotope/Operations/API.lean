import CORALean.ContSet.ConZonotope.Operations.Zonotope
import CORALean.ContSet.ConZonotope.Operations.Plus
import CORALean.ContSet.ConZonotope.Operations.And
import CORALean.ContSet.ConZonotope.Operations.Map
import CORALean.ContSet.ConZonotope.Operations.Mtimes
import CORALean.ContSet.ConZonotope.Operations.MtimesIntervalMat
import CORALean.ContSet.ConZonotope.Operations.LinComb
import CORALean.ContSet.ConZonotope.Operations.Reduce

/-!
# What `ConZonotope` computes

`and`, `plus`, `map` and `mtimes` keep the constraints and stay exact — `and`
being the one a zonotope cannot have. Multiplication by an interval matrix keeps
them too, and is outer for the zonotope's reason rather than for the
constraints'. `linComb` and `reduce` go through the enclosing zonotope and give
the constraints up, which is where the representation currently loses precision
that CORA does not.
-/
