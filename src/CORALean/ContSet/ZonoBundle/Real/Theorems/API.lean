module

public import CORALean.ContSet.ZonoBundle.Real.Theorems.BoxOuter
public import CORALean.ContSet.ZonoBundle.Real.Theorems.Basic
public import CORALean.ContSet.ZonoBundle.Real.Theorems.DirPcaCovarianceIsHermitian
public import CORALean.ContSet.ZonoBundle.Real.Theorems.EnclosingBoxContains
public import CORALean.ContSet.ZonoBundle.Real.Theorems.EnclosingParallelotopeOuter
public import CORALean.ContSet.ZonoBundle.Real.Theorems.IntervalAllContains
public import CORALean.ContSet.ZonoBundle.Real.Theorems.IntervalAllContainsIntervalSupportFunc
public import CORALean.ContSet.ZonoBundle.Real.Theorems.IntervalSupportFuncExact
public import CORALean.ContSet.ZonoBundle.Real.Theorems.IntervalSupportFuncOuter
public import CORALean.ContSet.ZonoBundle.Real.Theorems.FacetLiftOuter
public import CORALean.ContSet.ZonoBundle.Real.Theorems.FacetLiftStack
public import CORALean.ContSet.ZonoBundle.Real.Theorems.FacetLiftStackOuter
public import CORALean.ContSet.ZonoBundle.Real.Theorems.FlowIndexMax
public import CORALean.ContSet.ZonoBundle.Real.Theorems.GuardIntersectOuter
public import CORALean.ContSet.ZonoBundle.Real.Theorems.HullOuter
public import CORALean.ContSet.ZonoBundle.Real.Theorems.IntersectionExact
public import CORALean.ContSet.ZonoBundle.Real.Theorems.IntersectsOfIntersects
public import CORALean.ContSet.ZonoBundle.Real.Theorems.NotIntersectsImp
public import CORALean.ContSet.ZonoBundle.Real.Theorems.OfPointMemIff
public import CORALean.ContSet.ZonoBundle.Real.Theorems.ReduceOrder
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
public import CORALean.ContSet.ZonoBundle.Real.Theorems.ReplaceConstruct
public import CORALean.ContSet.ZonoBundle.Real.Theorems.CartProdExact
public import CORALean.ContSet.ZonoBundle.Real.Theorems.EnlargeOuter
public import CORALean.ContSet.ZonoBundle.Real.Theorems.ConstructEnlarge
public import CORALean.ContSet.ZonoBundle.Real.Theorems.ConstructEqIInter
public import CORALean.ContSet.ZonoBundle.Real.Theorems.IsequalConstruct
public import CORALean.ContSet.ZonoBundle.Real.Theorems.IsFullDimAllMembers
public import CORALean.ContSet.ZonoBundle.Real.Theorems.IsCenterMem
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
public import CORALean.ContSet.ZonoBundle.Real.Theorems.EncloseTightVerticesNonempty

/-!
# What a zonotope bundle guarantees, collected

What CORA's algorithms on a bundle give beyond an intersection. A bundle is `SetIntersection`
at its members, so the facts of every intersection are that class's, read at the members' own
guarantees in `Instances`: convexity (`convex_construct`), compactness given a member
(`isCompact_construct`, never a `CompactSet` instance, `k = 0` being `univ`), and the enclosures
of `plus`, `linComb`, `mtimes`, `mtimesMatZonotope`, `project`, `quadMap` and `reduce`
(`memberwise_outer`, `pairwise_outer`) and the exact `map` at a bijection
(`memberwise_image_exact`). Here: `intersection` exactly, through the general one;
`reduce_order_le`, each member at most `o * n` generators; `split_union`, exact at any
invertible `Λ` and enclosing box, and so each heuristic's split; the printed disjointness of the
halves is false (`split_not_disjoint`).
-/
