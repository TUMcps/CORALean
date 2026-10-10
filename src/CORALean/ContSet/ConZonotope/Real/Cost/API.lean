import CORALean.ContSet.ConZonotope.Real.Cost.Map
import CORALean.ContSet.ConZonotope.Real.Cost.Mtimes
import CORALean.ContSet.ConZonotope.Real.Cost.Reduce
import CORALean.ContSet.ConZonotope.Real.Cost.Plus
import CORALean.ContSet.ConZonotope.Real.Cost.Intersection
import CORALean.ContSet.ConZonotope.Real.Cost.LinComb
import CORALean.ContSet.ConZonotope.Real.Cost.MtimesIntervalMat

/-!
# What running `ConZonotope`'s operations costs

Scalar-operation counts against `Global/Cost.lean`'s model, one `def` per
operation, every one **asserted**. `Complexity/` is the other directory and the
other kind of claim: how large a *result* is, which is proved.

Seven operations. `map`, `mtimes` and `reduce` carry `P` over or drop it, so
they are `Zonotope`'s counts. `plus` and `mtimesIntervalMat` build their
polytope from `comap`s along block embeddings and one `intersection`, all free,
so they too equal `Zonotope`'s. `intersection` adds the `n * (h₂ + 1)` operations
that assemble the agreement equalities. `linComb` is the one that pays for its
constraints: both operands' `domain`s go through `HPolytope.halfScaled`, which
`HPolytope`'s `Cost/` prices **under the reading that a row is a dense vector**
(`HPolytope.halfScaledCost`); the count is exactly as good as that reading.

`reduceLift`, the constraint-keeping reduction, is not counted: it was not on
the main branch when these were written.

`ofPoint` and `ofMat` are left out as `Zonotope`'s constructors are: they place
data rather than compute it.
-/
