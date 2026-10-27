module

public import CORALean.ContSet.ZonoBundle.Float.Theorems.Basic
public import CORALean.ContSet.ZonoBundle.Float.Theorems.BoundDotLPLe
public import CORALean.ContSet.ZonoBundle.Float.Theorems.CartProdExact
public import CORALean.ContSet.ZonoBundle.Float.Theorems.ConstructEnlarge
public import CORALean.ContSet.ZonoBundle.Float.Theorems.ConstructEqIInter
public import CORALean.ContSet.ZonoBundle.Float.Theorems.ContainsPointSound
public import CORALean.ContSet.ZonoBundle.Float.Theorems.EmptyExact
public import CORALean.ContSet.ZonoBundle.Float.Theorems.EncloseTightOuter
public import CORALean.ContSet.ZonoBundle.Float.Theorems.EnclosingParallelotopeOuter
public import CORALean.ContSet.ZonoBundle.Float.Theorems.EnlargeOuter
public import CORALean.ContSet.ZonoBundle.Float.Theorems.IntersectionExact
public import CORALean.ContSet.ZonoBundle.Float.Theorems.IntervalAllContains
public import CORALean.ContSet.ZonoBundle.Float.Theorems.IntervalAllContainsIntervalSupportFunc
public import CORALean.ContSet.ZonoBundle.Float.Theorems.IntervalSupportFuncOuter
public import CORALean.ContSet.ZonoBundle.Float.Theorems.IsFullDimSound
public import CORALean.ContSet.ZonoBundle.Float.Theorems.IsequalSound
public import CORALean.ContSet.ZonoBundle.Float.Theorems.OriginExact
public import CORALean.ContSet.ZonoBundle.Float.Theorems.ParallelotopeContains
public import CORALean.ContSet.ZonoBundle.Float.Theorems.ReduceOrder
public import CORALean.ContSet.ZonoBundle.Float.Theorems.ReplaceConstruct
public import CORALean.ContSet.ZonoBundle.Float.Theorems.RepresentsaEmptySetSound
public import CORALean.ContSet.ZonoBundle.Float.Theorems.ShrinkOuter
public import CORALean.ContSet.ZonoBundle.Float.Theorems.SplitOuter
public import CORALean.ContSet.ZonoBundle.Float.Theorems.UnionSubsetLinComb

/-!
# What a float zonotope bundle guarantees, collected

Stated over the same sets of real points as the exact layer states them, each
member's rounding already inside its own `construct`. A bundle is `SetIntersection` at its
members, so what every intersection satisfies — convexity, compactness given a member, and the
enclosures of a bundle's `plus`, `linComb`, `mtimes`, `project`, `quadMap`, `reduce` and
`reindex`, which map or pair members — is a general theorem of that class read at the members'
own (`Instances.lean` reads it); this directory holds what CORA's own algorithms give beyond it.

`reduce_order_le` bounds each member of the reduced bundle at `o * n` generators, as
`Zonotope.reduceCombastel_order_le` does for one zonotope.
-/
