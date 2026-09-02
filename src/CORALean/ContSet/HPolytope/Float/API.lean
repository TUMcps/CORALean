import CORALean.ContSet.HPolytope.Float.HPolytope
import CORALean.ContSet.HPolytope.Float.Operations.API
import CORALean.ContSet.HPolytope.Float.Instances

/-!
# Halfspace descriptions over a floating-point scalar, collected

The one representation whose float layer differs from its exact one in shape:
`be` is an interval, because an equality has no slack of its own to round into.
-/
