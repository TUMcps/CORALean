import CORALean.ContSet.PolyZonotope.Float.Operations.GeneratorError
import CORALean.ContSet.PolyZonotope.Float.Operations.Plus
import CORALean.ContSet.PolyZonotope.Float.Operations.Mtimes
import CORALean.ContSet.PolyZonotope.Float.Operations.Compact
import CORALean.ContSet.PolyZonotope.Float.Operations.Dependent
import CORALean.ContSet.PolyZonotope.Float.Operations.LinComb
import CORALean.ContSet.PolyZonotope.Float.Operations.QuadMap
import CORALean.ContSet.PolyZonotope.Float.Operations.Reduce

/-!
# What `PolyZonotope` computes

`plus`, `linComb` and `mtimes` pay their rounding into the error box rather than
into new generators. `linComb` pays nothing on the dependent side: halving and
negation are exact, so all three dependent blocks are copies, and only the two
centre-derived vectors and the paired independent block round. `quadMap` cannot:
a quadratic map is not additive, so a box cannot travel through it beside the
nominal part, and `dependent` empties the box into generators first — the one
operation here that spends any.

`reduce` and the `compact` it runs first both *run* where the exact layer only
specifies: ranking generators needs a decidable order and merging columns needs
a decidable equality on them, and a machine scalar has both where ℝ has neither.
`compact` is the one operation whose two layers differ in what they cost —
merging adds entries, so it encloses here where over ℝ it is an equality.

None of the operations touches the exponent matrix numerically. It is a matrix of
naturals, every operation on it is exact, and the monomials of the nominal set
are therefore the exact layer's own.
-/
