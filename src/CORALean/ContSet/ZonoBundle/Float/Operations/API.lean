module

public import CORALean.ContSet.ZonoBundle.Float.Operations.Intersection
public import CORALean.ContSet.ZonoBundle.Float.Operations.Plus
public import CORALean.ContSet.ZonoBundle.Float.Operations.LinComb
public import CORALean.ContSet.ZonoBundle.Float.Operations.Mtimes
public import CORALean.ContSet.ZonoBundle.Float.Operations.MtimesIntervalMat
public import CORALean.ContSet.ZonoBundle.Float.Operations.Reindex
public import CORALean.ContSet.ZonoBundle.Float.Operations.Reduce
public import CORALean.ContSet.ZonoBundle.Float.Operations.SupportBound
public import CORALean.ContSet.ZonoBundle.Float.Operations.BoundDotLP
public import CORALean.ContSet.ZonoBundle.Float.Operations.Project
public import CORALean.ContSet.ZonoBundle.Float.Operations.Empty
public import CORALean.ContSet.ZonoBundle.Float.Operations.Origin
public import CORALean.ContSet.ZonoBundle.Float.Operations.Replace
public import CORALean.ContSet.ZonoBundle.Float.Operations.QuadMap
public import CORALean.ContSet.ZonoBundle.Float.Operations.CartProd
public import CORALean.ContSet.ZonoBundle.Float.Operations.Enlarge
public import CORALean.ContSet.ZonoBundle.Float.Operations.Isequal
public import CORALean.ContSet.ZonoBundle.Float.Operations.Split
public import CORALean.ContSet.ZonoBundle.Float.Operations.IsFullDim
public import CORALean.ContSet.ZonoBundle.Float.Operations.RepresentsaEmptySet
public import CORALean.ContSet.ZonoBundle.Float.Operations.ContainsPoint
public import CORALean.ContSet.ZonoBundle.Float.Operations.IntervalAll
public import CORALean.ContSet.ZonoBundle.Float.Operations.Parallelotope
public import CORALean.ContSet.ZonoBundle.Float.Operations.EnclosingParallelotope
public import CORALean.ContSet.ZonoBundle.Float.Operations.ReduceCombined
public import CORALean.ContSet.ZonoBundle.Float.Operations.Shrink
public import CORALean.ContSet.ZonoBundle.Float.Operations.EncloseTight

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
