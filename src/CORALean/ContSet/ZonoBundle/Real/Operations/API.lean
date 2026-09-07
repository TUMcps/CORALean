import CORALean.ContSet.ZonoBundle.Real.Operations.And
import CORALean.ContSet.ZonoBundle.Real.Operations.Plus
import CORALean.ContSet.ZonoBundle.Real.Operations.Mtimes
import CORALean.ContSet.ZonoBundle.Real.Operations.Map
import CORALean.ContSet.ZonoBundle.Real.Operations.OfPoint
import CORALean.ContSet.ZonoBundle.Real.Operations.SupportBound
import CORALean.ContSet.ZonoBundle.Real.Operations.Reduce

/-!
# What a zonotope bundle computes, collected

`and`, exact and the whole point of the representation; `plus` and `mtimes`,
both enclosures over the family, one component at a time; `map`, one linear
image per component, which `Instances` reads at a bijective one for `Reindex`;
and `ofPoint`, a bundle of one point-zonotope. `supportBound` answers a
direction without a linear program, taking the tightest of the family's own
component bounds, and needs the same `0 < B.k` compactness does. `reduce`
keeps the first `o` components and forgets the rest.
-/
