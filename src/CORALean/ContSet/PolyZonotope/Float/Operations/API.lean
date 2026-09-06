import CORALean.ContSet.PolyZonotope.Float.Operations.GeneratorError
import CORALean.ContSet.PolyZonotope.Float.Operations.Plus
import CORALean.ContSet.PolyZonotope.Float.Operations.Mtimes
import CORALean.ContSet.PolyZonotope.Float.Operations.Compact
import CORALean.ContSet.PolyZonotope.Float.Operations.Dependent
import CORALean.ContSet.PolyZonotope.Float.Operations.LinComb
import CORALean.ContSet.PolyZonotope.Float.Operations.QuadMap
import CORALean.ContSet.PolyZonotope.Float.Operations.Mul
import CORALean.ContSet.PolyZonotope.Float.Operations.EvalPoly
import CORALean.ContSet.PolyZonotope.Float.Operations.Reduce
import CORALean.ContSet.PolyZonotope.Float.Operations.RelaxExp
import CORALean.ContSet.PolyZonotope.Float.Operations.RelaxExpEven
import CORALean.ContSet.PolyZonotope.Float.Operations.RelaxExpMid
import CORALean.ContSet.PolyZonotope.Float.Operations.RelaxExpMulti
import CORALean.ContSet.PolyZonotope.Float.Operations.RelaxExpGreedy

/-!
# What `PolyZonotope` computes

`plus`, `linComb` and `mtimes` pay their rounding into the error box rather than into new
generators. `linComb` pays nothing on the dependent side: halving and negation are exact, so
all three dependent blocks are copies, and only the two centre-derived vectors and the paired
independent block round. `quadMap` cannot: a quadratic map is not additive, so a box cannot
travel through it beside the nominal part, and `dependent` empties the box into generators first.

`mul` carries that past degree two, spending it on one rounded product per
generator entry; `evalPoly` chains `mul` and prices the chaining itself.

`reduce` and the `compact` it runs first both *run* where the exact layer only specifies:
ranking needs a decidable order and merging columns a decidable equality, which a machine
scalar has and ℝ has not. `compact` alone differs in cost, merging adding entries.

`relaxExp` charges two column sums to the box and nothing else: its width is a count, not a
scalar, so the two layers relax by the same amount. `relaxExpEven` charges a third for the
centre it shifts, and `relaxExpMid` charges the same three at a shift with no sign to case on;
`relaxExpMulti` charges the first two at a width summed over every factor, and `relaxExpGreedy`
sequences steps and rounds nothing of its own.

No operation touches the exponent matrix numerically: it holds naturals, every
operation on it is exact, and the nominal set's monomials are the exact layer's.
-/
