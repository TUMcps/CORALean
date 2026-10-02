import CORALean.ContSet.ConZonotope.Float.Operations.Plus
import CORALean.ContSet.ConZonotope.Float.Operations.LinCombGDiff
import CORALean.ContSet.ConZonotope.Float.Operations.LinComb
import CORALean.ContSet.ConZonotope.Float.Operations.Project
import CORALean.ContSet.ConZonotope.Float.Operations.Reduce
import CORALean.ContSet.ConZonotope.Float.Operations.Empty
import CORALean.ContSet.ConZonotope.Float.Operations.Origin
import CORALean.ContSet.ConZonotope.Float.Operations.Reindex

/-!
# What the float `ConZonotope` computes

`plus` keeps the constraints, padding each onto the wider coefficient space, and
rounds only the centre. `linComb` keeps them too, weighting each side's rows and
unit box by the interpolation parameter; halving is exact, so the only rounding
is the centre's and the centre generator's. `reduce` goes through the enclosing
zonotope and gives the constraints up, as it does over ℝ.

`mtimes` and `intersection` are not here yet — see this directory's `API` for why.
-/
