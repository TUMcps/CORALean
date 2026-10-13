import CORALean.ContSet.VPolytope.Real.Complexity.Space.Plus
import CORALean.ContSet.VPolytope.Real.Complexity.Space.LinComb
import CORALean.ContSet.VPolytope.Real.Complexity.Space.Mtimes
import CORALean.ContSet.VPolytope.Real.Complexity.Space.Bilin
import CORALean.ContSet.VPolytope.Real.Complexity.Space.MtimesMatPolytope
import CORALean.ContSet.VPolytope.Real.Complexity.Space.Intersection

/-!
# What `VPolytope` costs

The size of an operation's result as a function of its operands' — vertex
count only, since a `VPolytope` has one vertex list. `plus`, `linComb`,
`mtimes`, `bilin` and `mtimesMatPolytope` are each `rfl` against the structure
instance in `Operations/`.

`intersection` is the exception: it goes out to halfspaces and enumerates vertices back,
so its count is `2 ^ m` on the rows the round trip built, or zero if that
turned out infeasible — `Intersection.lean` states both, since no single formula covers
the branch the operation's own `Nonempty` check decides.

`bilin_k_isBigO` puts `bilin`'s quadratic count in `O`-notation, the shape the
rest of this directory should eventually take.

The number of scalar operations each operation costs is not yet stated here.
-/
