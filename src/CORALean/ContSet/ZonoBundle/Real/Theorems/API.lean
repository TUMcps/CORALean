module

public import CORALean.ContSet.ZonoBundle.Real.Theorems.BoxOuter
public import CORALean.ContSet.ZonoBundle.Real.Theorems.Basic
public import CORALean.ContSet.ZonoBundle.Real.Theorems.DirPcaCovarianceIsHermitian
public import CORALean.ContSet.ZonoBundle.Real.Theorems.EnclosingBoxContains
public import CORALean.ContSet.ZonoBundle.Real.Theorems.EnclosingParallelotopeOuter
public import CORALean.ContSet.ZonoBundle.Real.Theorems.IntervalAllContains
public import CORALean.ContSet.ZonoBundle.Real.Theorems.FacetLiftOuter
public import CORALean.ContSet.ZonoBundle.Real.Theorems.FacetLiftStack
public import CORALean.ContSet.ZonoBundle.Real.Theorems.FacetLiftStackOuter
public import CORALean.ContSet.ZonoBundle.Real.Theorems.FlowIndexMax
public import CORALean.ContSet.ZonoBundle.Real.Theorems.GuardIntersectOuter
public import CORALean.ContSet.ZonoBundle.Real.Theorems.HullOuter
public import CORALean.ContSet.ZonoBundle.Real.Theorems.IntersectionExact
public import CORALean.ContSet.ZonoBundle.Real.Theorems.IntersectsOfIntersects
public import CORALean.ContSet.ZonoBundle.Real.Theorems.IsCompact
public import CORALean.ContSet.ZonoBundle.Real.Theorems.LinCombOuter
public import CORALean.ContSet.ZonoBundle.Real.Theorems.MapExact
public import CORALean.ContSet.ZonoBundle.Real.Theorems.MtimesMatZonotopeOuter
public import CORALean.ContSet.ZonoBundle.Real.Theorems.MtimesOuter
public import CORALean.ContSet.ZonoBundle.Real.Theorems.NotIntersectsImp
public import CORALean.ContSet.ZonoBundle.Real.Theorems.OfPointMemIff
public import CORALean.ContSet.ZonoBundle.Real.Theorems.PlusOuter
public import CORALean.ContSet.ZonoBundle.Real.Theorems.ReduceOrder
public import CORALean.ContSet.ZonoBundle.Real.Theorems.ReduceOuter
public import CORALean.ContSet.ZonoBundle.Real.Theorems.ShrinkOuter
public import CORALean.ContSet.ZonoBundle.Real.Theorems.SplitBoxUnion
public import CORALean.ContSet.ZonoBundle.Real.Theorems.SplitFilUnion
public import CORALean.ContSet.ZonoBundle.Real.Theorems.SplitFlowUnion
public import CORALean.ContSet.ZonoBundle.Real.Theorems.EmptyExact
public import CORALean.ContSet.ZonoBundle.Real.Theorems.SplitInter
public import CORALean.ContSet.ZonoBundle.Real.Theorems.SplitNotDisjoint
public import CORALean.ContSet.ZonoBundle.Real.Theorems.SplitPcaUnion
public import CORALean.ContSet.ZonoBundle.Real.Theorems.SplitUnion
public import CORALean.ContSet.ZonoBundle.Real.Theorems.SplitUnionEnclosingBox
public import CORALean.ContSet.ZonoBundle.Real.Theorems.ProjectOuter
public import CORALean.ContSet.ZonoBundle.Real.Theorems.ReplaceConstruct
public import CORALean.ContSet.ZonoBundle.Real.Theorems.QuadMapOuter
public import CORALean.ContSet.ZonoBundle.Real.Theorems.CartProdExact
public import CORALean.ContSet.ZonoBundle.Real.Theorems.EnlargeOuter
public import CORALean.ContSet.ZonoBundle.Real.Theorems.ConstructEnlarge
public import CORALean.ContSet.ZonoBundle.Real.Theorems.IsequalConstruct
public import CORALean.ContSet.ZonoBundle.Real.Theorems.IsFullDimAllMembers
public import CORALean.ContSet.ZonoBundle.Real.Theorems.IsCentreMem
public import CORALean.ContSet.ZonoBundle.Real.Theorems.ContainsAllIff
public import CORALean.ContSet.ZonoBundle.Real.Theorems.IsBoxOfForall
public import CORALean.ContSet.ZonoBundle.Real.Theorems.EncloseTightOuter
public import CORALean.ContSet.ZonoBundle.Real.Theorems.ConvHullExact
public import CORALean.ContSet.ZonoBundle.Real.Theorems.RepresentsaEmptySetIff
public import CORALean.ContSet.ZonoBundle.Real.Theorems.RepresentsaOriginIff
public import CORALean.ContSet.ZonoBundle.Real.Theorems.ExistsHPolytope
public import CORALean.ContSet.ZonoBundle.Real.Theorems.ConstructNeUniv
public import CORALean.ContSet.ZonoBundle.Real.Theorems.VolumeEqHPolytope
public import CORALean.ContSet.ZonoBundle.Real.Theorems.VolumeLeMember
public import CORALean.ContSet.ZonoBundle.Real.Theorems.EncloseTightPointsMem
public import CORALean.ContSet.ZonoBundle.Real.Theorems.ExistsHPolytopeConvHull

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
