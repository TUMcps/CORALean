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
import CORALean.ContSet.PolyZonotope.Real.Operations.EDrift
import CORALean.ContSet.PolyZonotope.Real.Operations.RelaxExp
import CORALean.ContSet.PolyZonotope.Real.Operations.RelaxExpEven
import CORALean.ContSet.PolyZonotope.Real.Operations.RelaxDrift
import CORALean.ContSet.PolyZonotope.Real.Operations.RelaxExpMid
import CORALean.ContSet.PolyZonotope.Real.Operations.RelaxExpMulti
import CORALean.ContSet.PolyZonotope.Real.Operations.ExpEdgeAt
import CORALean.ContSet.PolyZonotope.Real.Operations.ExpEdge
import CORALean.ContSet.PolyZonotope.Real.Operations.ExpGreedySel
import CORALean.ContSet.PolyZonotope.Real.Operations.RelaxExpGreedy

/-!
# What `PolyZonotope` computes

`plus`, `map` and `quadMap` exactly, `linComb` up to its independent block, and `dependent`,
which moves that block into the dependent one and is what lets `quadMap` be total.

`mul` multiplies two sets coordinatewise over shared factors, exact against `point` and not the
two sets; `quadMap` reaches degree two this way, `evalPoly` any degree.

Each of those grows the generator counts, and `compact` brings them back down without changing
the set: equal exponent columns add together, a generator that came out zero goes, and so does a
factor no column reads. `reduce` then cuts the count to an order the caller names, and loses.

`relaxExp` merges two dependent generators whose exponent columns agree off one index and pays
the difference into one new independent generator, at the price `eDiff` bounds: the count stays,
and the set is closer to a zonotope. `relaxExpEven` halves that price where the drift is
one-sided, `relaxExpMulti` drops the agreement and sums `eDiff` over every factor, and `eDrift`
brackets the drift on both sides, which `relaxDrift` reads as the midpoint and half-width that
`relaxExpMid` shifts and pays. `ExpEdgeAt` and `ExpEdge` are the graph of pairs worth merging,
and `relaxExpGreedy` walks it at whatever a selection names — `expGreedySel` being one that runs.

`plusE`, `linCombE` and `quadMapE` are the exponent matrices the size-changing operations
assemble, kept with the operations that build them so their lemmas read at plain counts rather
than at a projection. `identE` is the block `dependent` appends and a conversion's whole answer.
-/
