module

public import CORALean.ContSet.VPolytope.Real.Theorems.VertexMem
public import CORALean.ContSet.VPolytope.Real.Theorems.IntersectionOuter
public import CORALean.ContSet.VPolytope.Real.Theorems.Convex
public import CORALean.ContSet.VPolytope.Real.Theorems.ConvexHull
public import CORALean.ContSet.VPolytope.Real.Theorems.Basic
public import CORALean.ContSet.VPolytope.Real.Theorems.LinCombOuter
public import CORALean.ContSet.VPolytope.Real.Theorems.MapExact
public import CORALean.ContSet.VPolytope.Real.Theorems.MinkowskiDiffEqIInter
public import CORALean.ContSet.VPolytope.Real.Theorems.MtimesExact
public import CORALean.ContSet.VPolytope.Real.Theorems.BilinOuter
public import CORALean.ContSet.VPolytope.Real.Theorems.MtimesMatPolytopeOuter
public import CORALean.ContSet.VPolytope.Real.Theorems.PlusExact
public import CORALean.ContSet.VPolytope.Real.Theorems.PerturbSubset
public import CORALean.ContSet.VPolytope.Real.Theorems.SupportBoundAttained
public import CORALean.ContSet.VPolytope.Real.Theorems.ConvHullExact
public import CORALean.ContSet.VPolytope.Real.Theorems.IsFullDimIff
public import CORALean.ContSet.VPolytope.Real.Theorems.ProjectHighDimExact
public import CORALean.ContSet.VPolytope.Real.Theorems.CenterMem
public import CORALean.ContSet.VPolytope.Real.Theorems.CartProdExact
public import CORALean.ContSet.VPolytope.Real.Theorems.ConstructEqDropIff
public import CORALean.ContSet.VPolytope.Real.Theorems.ConstructEqIffOfInjective
public import CORALean.ContSet.VPolytope.Real.Theorems.InterIneqsNonemptyIff
public import CORALean.ContSet.VPolytope.Real.Theorems.InterNonemptyIff
public import CORALean.ContSet.VPolytope.Real.Theorems.InteriorEqEmptyIffRankLt
public import CORALean.ContSet.VPolytope.Real.Theorems.NotSubsetOfNotIsBounded
public import CORALean.ContSet.VPolytope.Real.Theorems.RestrictAffineHull
public import CORALean.ContSet.VPolytope.Real.Theorems.SetLinCombEqConvHull
public import CORALean.ContSet.VPolytope.Real.Theorems.SpanQrColsEqOfIndep
public import CORALean.ContSet.VPolytope.Real.Theorems.SubsetIffVertexMem
public import CORALean.ContSet.VPolytope.Real.Theorems.SubsetIneqsIff
public import CORALean.ContSet.VPolytope.Real.Theorems.SuccLeOfInteriorNonempty
public import CORALean.ContSet.VPolytope.Real.Theorems.SupportFuncEq
public import CORALean.ContSet.VPolytope.Real.Theorems.HausdorffDistEq
public import CORALean.ContSet.VPolytope.Real.Theorems.DistPointEq
public import CORALean.ContSet.VPolytope.Real.Theorems.KEqZeroOfConstructEqEmpty

/-!
# What `VPolytope` guarantees

`ConvexHull` is the pivot: once a vertex list is known to denote the hull of its
range, every other guarantee is hull algebra applied to `Set.range V`, and
`VertexMem` is the inclusion that gets it there.

`bilin_outer` is the one guarantee that is an outer inclusion rather than an
equality: not because anything is lost, but because the convex-hull equality
behind it is not proved here. `mtimesMatPolytope_outer` reads it back at `*ᵥ`.

`PerturbSubset` is what the float layer owes when it stores rounded vertices:
displacing every vertex by something a convex `D` admits widens the hull by no
more than `D`.

`MinkowskiDiffEqIInter` names no vertex representation of its own: a convex minuend's Minkowski
difference by a `VPolytope` needs only its vertices checked, one at a time.

`EncloseExact.lean` is deliberately not collected here: it states the generic `enclose` at the
vertex representation's instances, which `Instances.lean` declares after importing this file.
-/
