import CORALean.ContSet.Polytope.Operations.And
import CORALean.ContSet.Polytope.Operations.Comap
import CORALean.ContSet.Polytope.Operations.OfMat
import CORALean.ContSet.Polytope.Operations.UnitBox
import CORALean.ContSet.Polytope.Operations.Map
import CORALean.ContSet.Polytope.Operations.Mtimes
import CORALean.ContSet.Polytope.Operations.Plus
import CORALean.ContSet.Polytope.Operations.LinComb

/-!
# What the two polytope representations compute

Each operation sits with the representation that computes it exactly: `and` and
`comap` at halfspaces, `plus`, `map` and `linComb` at vertices. Neither list is
short of the other's by accident — converting between the representations is
vertex enumeration, which is not here.
-/
