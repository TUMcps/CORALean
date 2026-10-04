import CORALean.ContSet.ZonoBundle.Real.Theorems.BoxOuter
import CORALean.ContSet.ZonoBundle.Real.Theorems.Convex
import CORALean.ContSet.ZonoBundle.Real.Theorems.DirPcaCovarianceIsHermitian
import CORALean.ContSet.ZonoBundle.Real.Theorems.EnclosingBoxContains
import CORALean.ContSet.ZonoBundle.Real.Theorems.EnclosingParallelotopeOuter
import CORALean.ContSet.ZonoBundle.Real.Theorems.IntervalAllContains
import CORALean.ContSet.ZonoBundle.Real.Theorems.FacetLiftOuter
import CORALean.ContSet.ZonoBundle.Real.Theorems.FacetLiftStack
import CORALean.ContSet.ZonoBundle.Real.Theorems.FacetLiftStackOuter
import CORALean.ContSet.ZonoBundle.Real.Theorems.FlowIndexMax
import CORALean.ContSet.ZonoBundle.Real.Theorems.GuardIntersectOuter
import CORALean.ContSet.ZonoBundle.Real.Theorems.HullOuter
import CORALean.ContSet.ZonoBundle.Real.Theorems.IntersectionExact
import CORALean.ContSet.ZonoBundle.Real.Theorems.IntersectsOfIntersects
import CORALean.ContSet.ZonoBundle.Real.Theorems.IsBounded
import CORALean.ContSet.ZonoBundle.Real.Theorems.IsCompact
import CORALean.ContSet.ZonoBundle.Real.Theorems.LinCombOuter
import CORALean.ContSet.ZonoBundle.Real.Theorems.MapExact
import CORALean.ContSet.ZonoBundle.Real.Theorems.MtimesMatZonotopeOuter
import CORALean.ContSet.ZonoBundle.Real.Theorems.MtimesOuter
import CORALean.ContSet.ZonoBundle.Real.Theorems.NotIntersectsImp
import CORALean.ContSet.ZonoBundle.Real.Theorems.OfPointMem
import CORALean.ContSet.ZonoBundle.Real.Theorems.OfPointMemIff
import CORALean.ContSet.ZonoBundle.Real.Theorems.PlusOuter
import CORALean.ContSet.ZonoBundle.Real.Theorems.ReduceOrder
import CORALean.ContSet.ZonoBundle.Real.Theorems.ReduceOuter
import CORALean.ContSet.ZonoBundle.Real.Theorems.ReduceCombinedOuter
import CORALean.ContSet.ZonoBundle.Real.Theorems.ShrinkOuter
import CORALean.ContSet.ZonoBundle.Real.Theorems.SplitBoxUnion
import CORALean.ContSet.ZonoBundle.Real.Theorems.SplitFilUnion
import CORALean.ContSet.ZonoBundle.Real.Theorems.SplitFlowUnion
import CORALean.ContSet.ZonoBundle.Real.Theorems.EmptyExact
import CORALean.ContSet.ZonoBundle.Real.Theorems.SplitInter
import CORALean.ContSet.ZonoBundle.Real.Theorems.SplitNotDisjoint
import CORALean.ContSet.ZonoBundle.Real.Theorems.SplitPcaUnion
import CORALean.ContSet.ZonoBundle.Real.Theorems.SplitUnion
import CORALean.ContSet.ZonoBundle.Real.Theorems.SplitUnionEnclosingBox
import CORALean.ContSet.ZonoBundle.Real.Theorems.ProjectOuter
import CORALean.ContSet.ZonoBundle.Real.Theorems.ReplaceConstruct
import CORALean.ContSet.ZonoBundle.Real.Theorems.QuadMapOuter
import CORALean.ContSet.ZonoBundle.Real.Theorems.CartProdExact
import CORALean.ContSet.ZonoBundle.Real.Theorems.EnlargeOuter
import CORALean.ContSet.ZonoBundle.Real.Theorems.ConstructEnlarge
import CORALean.ContSet.ZonoBundle.Real.Theorems.IsequalConstruct
import CORALean.ContSet.ZonoBundle.Real.Theorems.IsequalCoraCounterexample

/-!
# What a zonotope bundle guarantees, collected

`intersection` exactly, `plus`, `linComb`, `mtimes` and `mtimesMatZonotope` as
enclosures, and convexity unconditionally. `map_exact` needs `f` bijective, not merely injective —
`Instances` supplies that at `reindexLin e` for `Reindex`. `isCompact_construct`
is a plain theorem at `0 < zB.k`, never a `CompactSet` instance:
`ZonoBundle.lean`'s docstring says why `k = 0` rules that out. `reduce_outer`
holds at any choice of survivors; `reduce_order_le` needs no such hypothesis,
unlike `Zonotope`'s. `split_union` is exact at any invertible `Λ` and enclosing box, and so
is each heuristic's split; the printed disjointness of the halves is false (`split_not_disjoint`).
-/
