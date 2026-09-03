import CORALean.ContSet.ConPolyZono.Real.API
import CORALean.ContSet.ConPolyZono.Float.API

/-!
# Constrained polynomial zonotopes

Kochdumper and Althoff (2020), and CORA's `conPolyZono`: a polynomial zonotope
whose factors additionally satisfy polynomial constraints, over the very same
factors the generators use.

What it buys over a polynomial zonotope is `and`: intersection, exactly, of sets
that need not be convex. `ConZonotope` buys the same operation for zonotopes,
and the two are the only representations here that intersect without loss.

One departure from the paper, and both layers turn on it: the right-hand side of
a constraint is an interval, so the row reads `A μ(α) ∈ b`. An equality is the
degenerate interval and nothing the paper states is lost, while a bound now has
a direction to be rounded in — which is what carries `and` across to the float
layer, and what lets a `ConZonotope`, inequalities and all, convert in exactly.
The representation's own docstring weighs that against the alternative.
-/
