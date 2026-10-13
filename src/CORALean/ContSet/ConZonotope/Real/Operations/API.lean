import CORALean.ContSet.ConZonotope.Real.Operations.Isequal
import CORALean.ContSet.ConZonotope.Real.Operations.OfMat
import CORALean.ContSet.ConZonotope.Real.Operations.MemOfMatIff
import CORALean.ContSet.ConZonotope.Real.Operations.Domain
import CORALean.ContSet.ConZonotope.Real.Operations.MemDomainIff
import CORALean.ContSet.ConZonotope.Real.Operations.Plus
import CORALean.ContSet.ConZonotope.Real.Operations.AgreeMat
import CORALean.ContSet.ConZonotope.Real.Operations.Intersection
import CORALean.ContSet.ConZonotope.Real.Operations.Map
import CORALean.ContSet.ConZonotope.Real.Operations.Mtimes
import CORALean.ContSet.ConZonotope.Real.Operations.MtimesEqMap
import CORALean.ContSet.ConZonotope.Real.Operations.MtimesIntervalMat
import CORALean.ContSet.ConZonotope.Real.Operations.LinComb
import CORALean.ContSet.ConZonotope.Real.Operations.Reduce
import CORALean.ContSet.ConZonotope.Real.Operations.KeepEmbed
import CORALean.ContSet.ConZonotope.Real.Operations.KeepInvolvement
import CORALean.ContSet.ConZonotope.Real.Operations.KeepMetric
import CORALean.ContSet.ConZonotope.Real.Operations.KeepRows
import CORALean.ContSet.ConZonotope.Real.Operations.KeepSlack
import CORALean.ContSet.ConZonotope.Real.Operations.KeepSplit
import CORALean.ContSet.ConZonotope.Real.Operations.ReduceKeep
import CORALean.ContSet.ConZonotope.Real.Operations.ReduceKeepBy
import CORALean.ContSet.ConZonotope.Real.Operations.LiftEq
import CORALean.ContSet.ConZonotope.Real.Operations.ReduceLiftBy
import CORALean.ContSet.ConZonotope.Real.Operations.ReduceLift
import CORALean.ContSet.ConZonotope.Real.Operations.OfPoint
import CORALean.ContSet.ConZonotope.Real.Operations.Enclose
import CORALean.ContSet.ConZonotope.Real.Operations.MinkDiffV
import CORALean.ContSet.ConZonotope.Real.Operations.IntersectHalfspace
import CORALean.ContSet.ConZonotope.Real.Operations.RowBound
import CORALean.ContSet.ConZonotope.Real.Operations.TightenCoeff
import CORALean.ContSet.ConZonotope.Real.Operations.TightenRow
import CORALean.ContSet.ConZonotope.Real.Operations.Tighten
import CORALean.ContSet.ConZonotope.Real.Operations.TightenCoeffER
import CORALean.ContSet.ConZonotope.Real.Operations.TightenPassER
import CORALean.ContSet.ConZonotope.Real.Operations.TightenER
import CORALean.ContSet.ConZonotope.Real.Operations.Eliminate
import CORALean.ContSet.ConZonotope.Real.Operations.Project
import CORALean.ContSet.ConZonotope.Real.Operations.ConstraintReduce
import CORALean.ContSet.ConZonotope.Real.Operations.PartialSolveLamG
import CORALean.ContSet.ConZonotope.Real.Operations.PartialSolveLamA
import CORALean.ContSet.ConZonotope.Real.Operations.PartialSolve
import CORALean.ContSet.ConZonotope.Real.Operations.Rescale
import CORALean.ContSet.ConZonotope.Real.Operations.Lift
import CORALean.ContSet.ConZonotope.Real.Operations.Empty
import CORALean.ContSet.ConZonotope.Real.Operations.CartProd
import CORALean.ContSet.ConZonotope.Real.Operations.Compact
import CORALean.ContSet.ConZonotope.Real.Operations.CompactEmbed
import CORALean.ContSet.ConZonotope.Real.Operations.CompactEqs
import CORALean.ContSet.ConZonotope.Real.Operations.CompactGens
import CORALean.ContSet.ConZonotope.Real.Operations.ConIntersect
import CORALean.ContSet.ConZonotope.Real.Operations.Split
import CORALean.ContSet.ConZonotope.Real.Operations.StripMat
import CORALean.ContSet.ConZonotope.Real.Operations.IntersectStrip
import CORALean.ContSet.ConZonotope.Real.Operations.IntersectStripFamily
import CORALean.ContSet.ConZonotope.Real.Operations.IntersectMany
import CORALean.ContSet.ConZonotope.Real.Operations.QuadMap
import CORALean.ContSet.ConZonotope.Real.Operations.SupportBound
import CORALean.ContSet.ConZonotope.Real.Operations.RepresentsaPoint
import CORALean.ContSet.ConZonotope.Real.Operations.RepresentsaOrigin
import CORALean.ContSet.ConZonotope.Real.Operations.RepresentsaEmptySet
import CORALean.ContSet.ConZonotope.Real.Operations.IsFullDimCora
import CORALean.ContSet.ConZonotope.Real.Operations.ContainsPoint
import CORALean.ContSet.ConZonotope.Real.Operations.IsCentre
import CORALean.ContSet.ConZonotope.Real.Operations.Stack
import CORALean.ContSet.ConZonotope.Real.Operations.NullPolytope
import CORALean.ContSet.ConZonotope.Real.Operations.CubLinearAt
import CORALean.ContSet.ConZonotope.Real.Operations.CubMap
import CORALean.ContSet.ConZonotope.Real.Operations.CubMapMixed
import CORALean.ContSet.ConZonotope.Real.Operations.SupportFuncUpperCora

/-!
# What `ConZonotope` computes

`intersection`, `plus`, `map` and `mtimes` keep the constraints and stay exact — `intersection`
being the one a zonotope cannot have. Multiplication by an interval matrix keeps them too, and is
outer for the zonotope's reason rather than for the constraints'. `linComb` keeps them as well,
weighting each side's constraints by the interpolation parameter; between two nonempty sets it is
the convex hull exactly, where the enclosing zonotope is only an enclosure of it.

`enclose` keeps them too, for the aligned pair `linComb` also covers, with one copy of `cZ₁.P`'s
own rows rather than a halfScaled intersection of both sides'; it is only outer, where `linComb`
is exact between nonempty sets.
`reduce` is the one operation that still goes through the enclosing zonotope and gives the
constraints up. CORA reduces the zonotope the constraint rows lift to and reads the rows back off
it, which asks for the equality system CORA's constraints are and this representation's polytope
need not be.

`OfMat` is CORA's constructor, whose constraints are an equality system, `Domain` is the
coefficient polytope the unit box and `P` make together, and `OfPoint` is the centre alone, at
`HPolytope.fullspace`. `MinkDiffV` folds `intersection` over a zonotope translated by each of a
polytope's vertices — Wetzlinger et al.'s Prop. 6, exact where every other difference here encloses.
`rowBound`, `tightenCoeff`, `tightenRow` and `tighten` are Raghuraman and Koeln's Algorithm 1;
`eliminate` is `Thm. 2`'s construction against it, solving one row for one coefficient.
Scott et al.: `constraintReduce` Prop. 5, `partialSolve` 4.2, `rescale` Prop. 4, `lift` Prop. 3.
-/
