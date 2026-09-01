import CORALean.ContSet.HPolytope.HPolytope
import CORALean.ContSet.HPolytope.Operations.API
import CORALean.ContSet.HPolytope.Theorems.API
import CORALean.ContSet.HPolytope.Instances

/-!
# Polytopes by halfspaces, collected

CORA's `polytope` with `isHRep` set. `VPolytope` is the same sets described by
vertices; the two are separate representations here, with no conversion between
them — converting either way is vertex enumeration, an algorithm in its own
right.

The specification only. A float layer would round the constraint bounds outward,
which for an inequality is well defined and for an equality is not — see
`ConZonotope`'s note.
-/
