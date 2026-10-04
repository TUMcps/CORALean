import CORALean.ContSet.ZonoBundle.Float.Operations.Intersection
import CORALean.ContSet.ZonoBundle.Float.Operations.Plus
import CORALean.ContSet.ZonoBundle.Float.Operations.LinComb
import CORALean.ContSet.ZonoBundle.Float.Operations.Mtimes
import CORALean.ContSet.ZonoBundle.Float.Operations.Reindex
import CORALean.ContSet.ZonoBundle.Float.Operations.Reduce
import CORALean.ContSet.ZonoBundle.Float.Operations.SupportBound
import CORALean.ContSet.ZonoBundle.Float.Operations.BoundDotLP
import CORALean.ContSet.ZonoBundle.Float.Operations.Project
import CORALean.ContSet.ZonoBundle.Float.Operations.Empty
import CORALean.ContSet.ZonoBundle.Float.Operations.Origin
import CORALean.ContSet.ZonoBundle.Float.Operations.Replace
import CORALean.ContSet.ZonoBundle.Float.Operations.QuadMap
import CORALean.ContSet.ZonoBundle.Float.Operations.CartProd
import CORALean.ContSet.ZonoBundle.Float.Operations.Enlarge
import CORALean.ContSet.ZonoBundle.Float.Operations.Isequal

/-!
# What a float zonotope bundle computes, collected

`intersection`, exact and the whole point of the representation; `plus`, `linComb` and
`mtimes`, enclosures over the family that leave each member's rounding in that
member's own error box; `reindex`, which does no arithmetic at all; and
`reduce`, which forgets members rather than absorbing them; and `supportBound`,
the least of the members' own float bounds; and `boundDotLP`, CORA's linear
program over the whole bundle, by a checked dual certificate.

`mtimesMatZonotope` is absent because `Zonotope` has no float counterpart to
build it from, and `ofPoint` because `OfPoint` asks for an arbitrary *real*
point, which no float representation in this tree can store — none instantiates
it.
-/
