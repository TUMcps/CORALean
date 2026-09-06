import CORALean.ContSet.ConZonotope.Float.Operations.Plus
import CORALean.ContSet.ConZonotope.Float.Operations.LinComb
import CORALean.ContSet.ConZonotope.Float.Operations.Reduce

/-!
# What the float `ConZonotope` computes

`plus` keeps the constraints, padding each onto the wider coefficient space, and
rounds only the centre. `linComb` keeps them too, weighting each side's rows and
unit box by the interpolation parameter; halving is exact, so the only rounding
is the centre's and the centre generator's. `reduce` goes through the enclosing
zonotope and gives the constraints up, as it does over ℝ.

`mtimes` and `and` are not here yet — see this directory's `API` for why.
-/
