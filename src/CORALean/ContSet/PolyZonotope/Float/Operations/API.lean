import CORALean.ContSet.PolyZonotope.Float.Operations.GeneratorError
import CORALean.ContSet.PolyZonotope.Float.Operations.Plus
import CORALean.ContSet.PolyZonotope.Float.Operations.Mtimes
import CORALean.ContSet.PolyZonotope.Float.Operations.Dependent
import CORALean.ContSet.PolyZonotope.Float.Operations.QuadMap
import CORALean.ContSet.PolyZonotope.Float.Operations.Reduce

/-!
# What `PolyZonotope` computes

`plus` and `mtimes` pay their rounding into the error box rather than into new
generators. `quadMap` cannot: a quadratic map is not additive, so a box cannot
travel through it beside the nominal part, and `dependent` empties the box into
generators first — the one operation here that spends any.

`reduce` is the one that runs where the exact layer only specifies: ranking
generators needs a decidable order, which a machine scalar has and ℝ does not.
Its docstring says why `compact` did not follow it across.

None of the operations touches the exponent matrix numerically. It is a matrix of
naturals, every operation on it is exact, and the monomials of the nominal set
are therefore the exact layer's own.
-/
