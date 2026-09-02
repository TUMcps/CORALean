import CORALean.ContSet.ConZonotope.Float.Operations.Plus
import CORALean.ContSet.ConZonotope.Float.Operations.LinComb
import CORALean.ContSet.ConZonotope.Float.Operations.Reduce

/-!
# What the float `ConZonotope` computes

`plus` keeps the constraints, padding each onto the wider coefficient space, and
rounds only the centre. `linComb` and `reduce` go through the enclosing zonotope
and give the constraints up, as they do over ℝ.

`mtimes` and `and` are not here yet — see this directory's `API` for why.
-/
