import CORALean.ContSet.PolyZonotope.Real.Operations.Map
import CORALean.ContSet.PolyZonotope.Real.Operations.Mtimes
import CORALean.ContSet.PolyZonotope.Real.Operations.Plus
import CORALean.ContSet.PolyZonotope.Real.Operations.LinComb
import CORALean.ContSet.PolyZonotope.Real.Operations.Dependent
import CORALean.ContSet.PolyZonotope.Real.Operations.QuadMap

/-!
# What `PolyZonotope` computes

`plus`, `map` and `quadMap` exactly, `linComb` up to its independent block, and
`dependent`, which moves that block into the dependent one and is what lets
`quadMap` be total. Each grows the generator counts and nothing here shrinks
them: there is no `reduce`.

`plusE`, `linCombE` and `quadMapE` are the exponent matrices the size-changing
operations assemble, kept in the files of the operations that build them so that
their lemmas are stated at plain counts rather than at a projection.
-/
