import CORALean.ContSet.PolyZonotope.Real.Operations.IdentE
import CORALean.ContSet.PolyZonotope.Real.Operations.Map
import CORALean.ContSet.PolyZonotope.Real.Operations.Mtimes
import CORALean.ContSet.PolyZonotope.Real.Operations.Plus
import CORALean.ContSet.PolyZonotope.Real.Operations.LinComb
import CORALean.ContSet.PolyZonotope.Real.Operations.Dependent
import CORALean.ContSet.PolyZonotope.Real.Operations.Point
import CORALean.ContSet.PolyZonotope.Real.Operations.QuadMap
import CORALean.ContSet.PolyZonotope.Real.Operations.Mul
import CORALean.ContSet.PolyZonotope.Real.Operations.Compact
import CORALean.ContSet.PolyZonotope.Real.Operations.Reduce

/-!
# What `PolyZonotope` computes

`plus`, `map` and `quadMap` exactly, `linComb` up to its independent block, and
`dependent`, which moves that block into the dependent one and is what lets
`quadMap` be total.

`mul` multiplies two sets coordinatewise over shared factors, which is `quadMap`
carried past degree two. It is exact against `point` — the map a factor vector
picks a point out by — and not against the two sets, which is what shared
factors force.

Each of those grows the generator counts, and `compact` is what brings them back
down without changing the set: equal exponent columns are one monomial and are
added together, a generator that came out zero goes, and so does a factor no
column reads. `reduce` then brings the dependent count to an order the caller
names, which is the one operation here that loses something.

`plusE`, `linCombE` and `quadMapE` are the exponent matrices the size-changing
operations assemble, kept in the files of the operations that build them so that
their lemmas are stated at plain counts rather than at a projection. `identE` is
the exception, being the block `dependent` appends and a conversion's whole
answer.
-/
