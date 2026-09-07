import CORALean.ContSet.HPolytope.Real.HPolytope
import CORALean.ContSet.HPolytope.Real.Operations.API
import CORALean.ContSet.HPolytope.Real.Theorems.API
import CORALean.ContSet.HPolytope.Real.Complexity.API
import CORALean.ContSet.HPolytope.Real.Instances

/-!
# Polytopes by halfspaces, collected

CORA's `polytope` with `isHRep` set. `VPolytope` is the same sets by vertices,
a separate representation, converting either way only by vertex enumeration, an
algorithm in its own right.

Both layers are specified. Rounding lands differently here than in the
representations above, in `Float`.

An inequality absorbs its rounding the way an `Interval` does: raise `b`, account
for the rounding of `A`, and the halfspace only grows. An equality has no slack to
raise — any rounding of `Ae` or `be` names a different hyperplane, and a
hyperplane has empty interior. So the float `be` is an *interval*, read as
`Ae x ∈ be`: one row per equality still, CORA's shape kept, and the slack put
where the rounding happens.

An `InflatedContSet` error box does **not** work here. That box is added in the
ambient space, after the constraints have already chosen `x`; rounding an
equality system can make it infeasible while the exact one is satisfiable —
`A = [[1],[3]]`, `b = [1/3, 1]` is satisfied by `β = 1/3` and by nothing at all
once `b₁` is rounded — and `∅` plus a box is still `∅`. Slack on a constraint
has to live on that constraint, and `ConZonotope` inherits that, its coefficient
domain being one of these.
-/
