module

public import CORALean.ContSet.ZonoBundle.Float.Theorems.Basic
public import CORALean.ContSet.ZonoBundle.Float.Theorems.BoundDotLPLe
public import CORALean.ContSet.ZonoBundle.Float.Theorems.CartProdExact
public import CORALean.ContSet.ZonoBundle.Float.Theorems.ConstructEnlarge
public import CORALean.ContSet.ZonoBundle.Float.Theorems.ContainsPointSound
public import CORALean.ContSet.ZonoBundle.Float.Theorems.Convex
public import CORALean.ContSet.ZonoBundle.Float.Theorems.EmptyExact
public import CORALean.ContSet.ZonoBundle.Float.Theorems.EncloseTightOuter
public import CORALean.ContSet.ZonoBundle.Float.Theorems.EnclosingParallelotopeOuter
public import CORALean.ContSet.ZonoBundle.Float.Theorems.EnlargeOuter
public import CORALean.ContSet.ZonoBundle.Float.Theorems.IntersectionExact
public import CORALean.ContSet.ZonoBundle.Float.Theorems.IntervalAllContains
public import CORALean.ContSet.ZonoBundle.Float.Theorems.IsCompact
public import CORALean.ContSet.ZonoBundle.Float.Theorems.IsFullDimSound
public import CORALean.ContSet.ZonoBundle.Float.Theorems.IsequalSound
public import CORALean.ContSet.ZonoBundle.Float.Theorems.LinCombOuter
public import CORALean.ContSet.ZonoBundle.Float.Theorems.MtimesIntervalMatOuter
public import CORALean.ContSet.ZonoBundle.Float.Theorems.MtimesOuter
public import CORALean.ContSet.ZonoBundle.Float.Theorems.OriginExact
public import CORALean.ContSet.ZonoBundle.Float.Theorems.ParallelotopeContains
public import CORALean.ContSet.ZonoBundle.Float.Theorems.PlusOuter
public import CORALean.ContSet.ZonoBundle.Float.Theorems.ProjectOuter
public import CORALean.ContSet.ZonoBundle.Float.Theorems.QuadMapOuter
public import CORALean.ContSet.ZonoBundle.Float.Theorems.ReduceOrder
public import CORALean.ContSet.ZonoBundle.Float.Theorems.ReduceOuter
public import CORALean.ContSet.ZonoBundle.Float.Theorems.ReindexExact
public import CORALean.ContSet.ZonoBundle.Float.Theorems.ReplaceConstruct
public import CORALean.ContSet.ZonoBundle.Float.Theorems.RepresentsaEmptySetSound
public import CORALean.ContSet.ZonoBundle.Float.Theorems.ShrinkOuter
public import CORALean.ContSet.ZonoBundle.Float.Theorems.SplitOuter
public import CORALean.ContSet.ZonoBundle.Float.Theorems.UnionSubsetLinComb

/-!
# What a float zonotope bundle guarantees, collected

Stated over the same sets of real points as the exact layer states them, each
member's rounding already inside its own `construct`. `intersection` and `reindex` are
exact; `plus`, `linComb` and `mtimes` are enclosures, the pairwise or
componentwise ones the exact layer had plus what the members rounded.

`reduce_outer` holds at any choice of survivors, and `reduce_order_le` needs no
`0 < o`, unlike `Zonotope.reduceCombastel_order_le`: a bundle of `k = 0` is
`univ`, which encloses anything. `reindex_exact` and `isCompact_construct` are
where `k = 0` costs something instead — the first is why `Set.image_iInter` is
taken at a bijection, the second why compactness is stated under `0 < zB.k`.
-/
