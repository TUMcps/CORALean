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

The specification only, and a float layer needs a decision first. An inequality
relaxes soundly — raise `b`, account for the rounding of `A`, and the halfspace
only grows. An equality does not: any rounding of `Ae` or `be` names a different
hyperplane, and a hyperplane has empty interior, so the rounded set and the exact
one generally meet in less than either. The two sound treatments are different
representations — turn every equality into two relaxed inequalities, so the float
description is inequality-only; or carry an `InflatedContSet` error box, as the
float zonotope does. `ConZonotope` inherits whichever is chosen, its domain being
one of these.
-/
