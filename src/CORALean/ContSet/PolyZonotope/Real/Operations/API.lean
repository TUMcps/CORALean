import CORALean.ContSet.PolyZonotope.Real.Operations.IdentE
import CORALean.ContSet.PolyZonotope.Real.Operations.Map
import CORALean.ContSet.PolyZonotope.Real.Operations.Mtimes
import CORALean.ContSet.PolyZonotope.Real.Operations.Plus
import CORALean.ContSet.PolyZonotope.Real.Operations.LinComb
import CORALean.ContSet.PolyZonotope.Real.Operations.Dependent
import CORALean.ContSet.PolyZonotope.Real.Operations.Point
import CORALean.ContSet.PolyZonotope.Real.Operations.QuadMap
import CORALean.ContSet.PolyZonotope.Real.Operations.Mul
import CORALean.ContSet.PolyZonotope.Real.Operations.EvalPoly
import CORALean.ContSet.PolyZonotope.Real.Operations.Compact
import CORALean.ContSet.PolyZonotope.Real.Operations.Reduce
import CORALean.ContSet.PolyZonotope.Real.Operations.EDiff
import CORALean.ContSet.PolyZonotope.Real.Operations.RelaxExp

/-!
# What `PolyZonotope` computes

`plus`, `map` and `quadMap` exactly, `linComb` up to its independent block, and
`dependent`, which moves that block into the dependent one and is what lets
`quadMap` be total.

`mul` multiplies two sets coordinatewise over shared factors, exact against
`point` and not the two sets; `quadMap` reaches degree two this way, `evalPoly` any degree.

Each of those grows the generator counts, and `compact` brings them back down
without changing the set: equal exponent columns are one monomial and are added
together, a generator that came out zero goes, and so does a factor no column
reads. `reduce` then brings the dependent count to an order the caller names,
the one operation here that loses something.

`relaxExp` merges two dependent generators whose exponent columns agree off one
index and pays the difference into one new independent generator, at the price
`eDiff` bounds: the count is where it was, and the set is closer to a zonotope.

`plusE`, `linCombE` and `quadMapE` are the exponent matrices the size-changing
operations assemble, kept with the operations that build them so their lemmas
are stated at plain counts rather than at a projection. `identE` is the
exception, being the block `dependent` appends and a conversion's whole answer.
-/
