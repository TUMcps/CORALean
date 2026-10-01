import CORALean.ContSet.ConZonotope.Real.Theorems.MemConstruct
import CORALean.ContSet.ConZonotope.Real.Theorems.ConstructEqImage
import CORALean.ContSet.ConZonotope.Real.Theorems.PlusExact
import CORALean.ContSet.ConZonotope.Real.Theorems.IntersectionExact
import CORALean.ContSet.ConZonotope.Real.Theorems.ConstructFoldlIntersectionEq
import CORALean.ContSet.ConZonotope.Real.Theorems.MapExact
import CORALean.ContSet.ConZonotope.Real.Theorems.MtimesExact
import CORALean.ContSet.ConZonotope.Real.Theorems.MtimesIntervalMatOuter
import CORALean.ContSet.ConZonotope.Real.Theorems.AbsSmulCoeffLeOne
import CORALean.ContSet.ConZonotope.Real.Theorems.SumUnivLinComb
import CORALean.ContSet.ConZonotope.Real.Theorems.LinCombOuter
import CORALean.ContSet.ConZonotope.Real.Theorems.LinCombInner
import CORALean.ContSet.ConZonotope.Real.Theorems.ReduceOuter
import CORALean.ContSet.ConZonotope.Real.Theorems.ReduceOrder
import CORALean.ContSet.ConZonotope.Real.Theorems.KeepRowsMem
import CORALean.ContSet.ConZonotope.Real.Theorems.ReduceKeepByOuter
import CORALean.ContSet.ConZonotope.Real.Theorems.ReduceKeepOrder
import CORALean.ContSet.ConZonotope.Real.Theorems.ReduceKeepOuter
import CORALean.ContSet.ConZonotope.Real.Theorems.EncloseOuter
import CORALean.ContSet.ConZonotope.Real.Theorems.Convex
import CORALean.ContSet.ConZonotope.Real.Theorems.IsCompactDomain
import CORALean.ContSet.ConZonotope.Real.Theorems.IsCompact
import CORALean.ContSet.ConZonotope.Real.Theorems.IsClosed
import CORALean.ContSet.ConZonotope.Real.Theorems.IsBounded
import CORALean.ContSet.ConZonotope.Real.Theorems.OfPointMem
import CORALean.ContSet.ConZonotope.Real.Theorems.IsAffineImageIff
import CORALean.ContSet.ConZonotope.Real.Theorems.IntersectsHyperplaneIff
import CORALean.ContSet.ConZonotope.Real.Theorems.MinkDiffVExact
import CORALean.ContSet.ConZonotope.Real.Theorems.IneqsContainsIff
import CORALean.ContSet.ConZonotope.Real.Theorems.ExistsIsGreatestIneqs
import CORALean.ContSet.ConZonotope.Real.Theorems.InterIneqsNonemptyIff
import CORALean.ContSet.ConZonotope.Real.Theorems.IntersectHalfspaceExact
import CORALean.ContSet.ConZonotope.Real.Theorems.TightenOuter
import CORALean.ContSet.ConZonotope.Real.Theorems.TightenOuterSafe
import CORALean.ContSet.ConZonotope.Real.Theorems.EliminateExact
import CORALean.ContSet.ConZonotope.Real.Theorems.OfPointMemIff
import CORALean.ContSet.ConZonotope.Real.Theorems.ProjectExact
import CORALean.ContSet.ConZonotope.Real.Theorems.ConstraintReduceSumSmulMulVec
import CORALean.ContSet.ConZonotope.Real.Theorems.ConstraintReduceOuter
import CORALean.ContSet.ConZonotope.Real.Theorems.ConstraintReduceOneMemIff
import CORALean.ContSet.ConZonotope.Real.Theorems.PartialSolveLamGMulVec
import CORALean.ContSet.ConZonotope.Real.Theorems.PartialSolveLamAMul
import CORALean.ContSet.ConZonotope.Real.Theorems.PartialSolveLamAMulVec
import CORALean.ContSet.ConZonotope.Real.Theorems.MemOfMatDropIff
import CORALean.ContSet.ConZonotope.Real.Theorems.PartialSolveZeroCol
import CORALean.ContSet.ConZonotope.Real.Theorems.PartialSolveZeroRow
import CORALean.ContSet.ConZonotope.Real.Theorems.PartialSolveEqEliminate
import CORALean.ContSet.ConZonotope.Real.Theorems.EliminateOuter
import CORALean.ContSet.ConZonotope.Real.Theorems.RescaleExact
import CORALean.ContSet.ConZonotope.Real.Theorems.LiftIff
import CORALean.ContSet.ConZonotope.Real.Theorems.MemLiftZeroIff
import CORALean.ContSet.ConZonotope.Real.Theorems.LiftThenReduce
import CORALean.ContSet.ConZonotope.Real.Theorems.ExistsFeasibleIffIsLeast
import CORALean.ContSet.ConZonotope.Real.Theorems.NonemptyIffIsLeast
import CORALean.ContSet.ConZonotope.Real.Theorems.MemIffIsLeast

/-!
# What `ConZonotope` guarantees

`intersection`, `plus` and `map` exactly; the interval-matrix product and `reduce` as enclosures,
`reduce` by way of `zonotope_contains`, and `reduce_order_le` for its own generator-count bound.
`linComb` has both directions: `_outer` is what the interface asks for and holds always, `_inner`
is what says the result is the convex hull itself and asks both sets to be nonempty. `enclose_outer`
is the one direction `enclose` gets, asking the constraints to agree besides. The topological facts
go through `ConstructEqImage` and so through the polytope, which is where they differ from a
zonotope's. `OfPointMem` needs no theorem of `HPolytope`'s: an empty row index discharges the
constraint the same way it discharges the generator sum. `IsAffineImageIff` is the representation
itself characterized: exactly the bounded affine images of a polytope, `ConstructEqImage` and
`HPolytope`'s own conversion read as the two halves of one iff. `IntersectsHyperplaneIff` reads
`convex_construct` as a hyperplane test. `ConstructFoldlIntersectionEq` reads `intersection_exact`
along a fold: any finite conjunction of constrained-zonotope memberships is itself one.
`MinkDiffVExact` is that fold applied to a zonotope translated by a polytope's vertices — Prop. 6,
an equality rather than an enclosure.
`IneqsContainsIff` and `InterIneqsNonemptyIff` are the containment and intersection checks a
specification asks for, each an equivalence with one linear program's optimum, taken as a
hypothesis as the paper's own `max`/`min` do; `ExistsIsGreatestIneqs` supplies the first.
`TightenOuter` is `tighten`'s soundness, Algorithm 1's own guarantee; `TightenOuterSafe` is the
same restricted to a dependency-closed set, and `EliminateExact` is `Thm. 2` itself under it.
Scott et al.'s Props. 2-5, Sec. 4.2-4.3: `NonemptyIffIsLeast`, `LiftIff`, `RescaleExact`,
`ConstraintReduceOuter`, `EliminateOuter`, `LiftThenReduce`.
-/
