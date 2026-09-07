import CORALean.ContSet.ZonoBundle.Float.Operations.And
import CORALean.ContSet.ZonoBundle.Float.Operations.Plus
import CORALean.ContSet.ZonoBundle.Float.Operations.LinComb
import CORALean.ContSet.ZonoBundle.Float.Operations.Mtimes
import CORALean.ContSet.ZonoBundle.Float.Operations.Reindex
import CORALean.ContSet.ZonoBundle.Float.Operations.Reduce

/-!
# What a float zonotope bundle computes, collected

`and`, exact and the whole point of the representation; `plus`, `linComb` and
`mtimes`, enclosures over the family that leave each member's rounding in that
member's own error box; `reindex`, which does no arithmetic at all; and
`reduce`, which forgets members rather than absorbing them.

`mtimesMatZonotope` is absent because `Zonotope` has no float counterpart to
build it from, and `ofPoint` because `OfPoint` asks for an arbitrary *real*
point, which no float representation in this tree can store — none instantiates
it. `supportBound` waits on a float zonotope bound to take the minimum of.
-/
