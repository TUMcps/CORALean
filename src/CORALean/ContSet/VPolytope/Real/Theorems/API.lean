import CORALean.ContSet.VPolytope.Real.Theorems.VertexMem
import CORALean.ContSet.VPolytope.Real.Theorems.IntersectionOuter
import CORALean.ContSet.VPolytope.Real.Theorems.Convex
import CORALean.ContSet.VPolytope.Real.Theorems.ConvexHull
import CORALean.ContSet.VPolytope.Real.Theorems.IsCompact
import CORALean.ContSet.VPolytope.Real.Theorems.IsClosed
import CORALean.ContSet.VPolytope.Real.Theorems.IsBounded
import CORALean.ContSet.VPolytope.Real.Theorems.LinCombOuter
import CORALean.ContSet.VPolytope.Real.Theorems.MapExact
import CORALean.ContSet.VPolytope.Real.Theorems.MinkowskiDiffEqIInter
import CORALean.ContSet.VPolytope.Real.Theorems.MtimesExact
import CORALean.ContSet.VPolytope.Real.Theorems.BilinOuter
import CORALean.ContSet.VPolytope.Real.Theorems.MatPolytopeExact
import CORALean.ContSet.VPolytope.Real.Theorems.MtimesMatPolytopeOuter
import CORALean.ContSet.VPolytope.Real.Theorems.PlusExact
import CORALean.ContSet.VPolytope.Real.Theorems.PerturbSubset
import CORALean.ContSet.VPolytope.Real.Theorems.SupportBoundAttained
import CORALean.ContSet.VPolytope.Real.Theorems.ProjectExact
import CORALean.ContSet.VPolytope.Real.Theorems.EnclosePointsExact
import CORALean.ContSet.VPolytope.Real.Theorems.ConvHullExact
import CORALean.ContSet.VPolytope.Real.Theorems.OrExact
import CORALean.ContSet.VPolytope.Real.Theorems.IsFullDimIff
import CORALean.ContSet.VPolytope.Real.Theorems.ProjectHighDimExact
import CORALean.ContSet.VPolytope.Real.Theorems.CenterMem
import CORALean.ContSet.VPolytope.Real.Theorems.CartProdExact
import CORALean.ContSet.VPolytope.Real.Theorems.ConstructEqDropIff
import CORALean.ContSet.VPolytope.Real.Theorems.ConstructEqIffCounterexample
import CORALean.ContSet.VPolytope.Real.Theorems.ConstructEqIffOfInjective
import CORALean.ContSet.VPolytope.Real.Theorems.InterIneqsNonemptyIff
import CORALean.ContSet.VPolytope.Real.Theorems.InterNonemptyIff
import CORALean.ContSet.VPolytope.Real.Theorems.InteriorEqEmptyIffRankLt
import CORALean.ContSet.VPolytope.Real.Theorems.NotSubsetOfNotIsBounded
import CORALean.ContSet.VPolytope.Real.Theorems.RestrictAffineHull
import CORALean.ContSet.VPolytope.Real.Theorems.SegmentsConvHullCounterexample
import CORALean.ContSet.VPolytope.Real.Theorems.SegmentsEqConvHull
import CORALean.ContSet.VPolytope.Real.Theorems.SpanQrColsCounterexample
import CORALean.ContSet.VPolytope.Real.Theorems.SpanQrColsEqOfIndep
import CORALean.ContSet.VPolytope.Real.Theorems.SubsetIffVertexMem
import CORALean.ContSet.VPolytope.Real.Theorems.SubsetIneqsIff
import CORALean.ContSet.VPolytope.Real.Theorems.SuccLeOfInteriorNonempty
import CORALean.ContSet.VPolytope.Real.Theorems.SupportFuncEq
import CORALean.ContSet.VPolytope.Real.Theorems.HausdorffDistEq
import CORALean.ContSet.VPolytope.Real.Theorems.DistPointEq
import CORALean.ContSet.VPolytope.Real.Theorems.KEqZeroOfConstructEqEmpty
import CORALean.ContSet.VPolytope.Real.Theorems.RepresentsaHalfspaceCoraCrash

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
