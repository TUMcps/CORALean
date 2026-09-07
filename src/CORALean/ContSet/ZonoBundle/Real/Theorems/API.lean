import CORALean.ContSet.ZonoBundle.Real.Theorems.IntersectionExact
import CORALean.ContSet.ZonoBundle.Real.Theorems.PlusOuter
import CORALean.ContSet.ZonoBundle.Real.Theorems.LinCombOuter
import CORALean.ContSet.ZonoBundle.Real.Theorems.MtimesOuter
import CORALean.ContSet.ZonoBundle.Real.Theorems.MtimesMatZonotopeOuter
import CORALean.ContSet.ZonoBundle.Real.Theorems.MapExact
import CORALean.ContSet.ZonoBundle.Real.Theorems.OfPointMem
import CORALean.ContSet.ZonoBundle.Real.Theorems.Convex
import CORALean.ContSet.ZonoBundle.Real.Theorems.IsCompact
import CORALean.ContSet.ZonoBundle.Real.Theorems.ReduceOuter
import CORALean.ContSet.ZonoBundle.Real.Theorems.ReduceOrder

/-!
# What a zonotope bundle guarantees, collected

`intersection` exactly, `plus`, `linComb`, `mtimes` and `mtimesMatZonotope` as
enclosures, and convexity unconditionally. `map_exact` needs `f` bijective, not merely injective —
`Instances` supplies that at `reindexLin e` for `Reindex`. `isCompact_construct`
is a plain theorem at `0 < zB.k`, never a `CompactSet` instance:
`ZonoBundle.lean`'s docstring says why `k = 0` rules that out. `reduce_outer`
holds at any choice of survivors; `reduce_order_le` needs no such hypothesis,
unlike `Zonotope`'s.
-/
