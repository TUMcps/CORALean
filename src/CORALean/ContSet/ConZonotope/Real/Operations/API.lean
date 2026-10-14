module

public import CORALean.ContSet.ConZonotope.Real.Operations.Isequal
public import CORALean.ContSet.ConZonotope.Real.Operations.OfMat
public import CORALean.ContSet.ConZonotope.Real.Operations.MemOfMatIff
public import CORALean.ContSet.ConZonotope.Real.Operations.Domain
public import CORALean.ContSet.ConZonotope.Real.Operations.MemDomainIff
public import CORALean.ContSet.ConZonotope.Real.Operations.Plus
public import CORALean.ContSet.ConZonotope.Real.Operations.AgreeMat
public import CORALean.ContSet.ConZonotope.Real.Operations.Intersection
public import CORALean.ContSet.ConZonotope.Real.Operations.Map
public import CORALean.ContSet.ConZonotope.Real.Operations.Mtimes
public import CORALean.ContSet.ConZonotope.Real.Operations.Basic
public import CORALean.ContSet.ConZonotope.Real.Operations.MtimesIntervalMat
public import CORALean.ContSet.ConZonotope.Real.Operations.LinComb
public import CORALean.ContSet.ConZonotope.Real.Operations.Reduce
public import CORALean.ContSet.ConZonotope.Real.Operations.KeepEmbed
public import CORALean.ContSet.ConZonotope.Real.Operations.KeepInvolvement
public import CORALean.ContSet.ConZonotope.Real.Operations.KeepMetric
public import CORALean.ContSet.ConZonotope.Real.Operations.KeepRows
public import CORALean.ContSet.ConZonotope.Real.Operations.KeepSlack
public import CORALean.ContSet.ConZonotope.Real.Operations.KeepSplit
public import CORALean.ContSet.ConZonotope.Real.Operations.ReduceKeep
public import CORALean.ContSet.ConZonotope.Real.Operations.ReduceKeepBy
public import CORALean.ContSet.ConZonotope.Real.Operations.LiftEq
public import CORALean.ContSet.ConZonotope.Real.Operations.ReduceLiftBy
public import CORALean.ContSet.ConZonotope.Real.Operations.ReduceLift
public import CORALean.ContSet.ConZonotope.Real.Operations.OfPoint
public import CORALean.ContSet.ConZonotope.Real.Operations.Enclose
public import CORALean.ContSet.ConZonotope.Real.Operations.MinkDiffV
public import CORALean.ContSet.ConZonotope.Real.Operations.IntersectHalfspace
public import CORALean.ContSet.ConZonotope.Real.Operations.RowBound
public import CORALean.ContSet.ConZonotope.Real.Operations.TightenCoeff
public import CORALean.ContSet.ConZonotope.Real.Operations.TightenRow
public import CORALean.ContSet.ConZonotope.Real.Operations.Tighten
public import CORALean.ContSet.ConZonotope.Real.Operations.TightenCoeffER
public import CORALean.ContSet.ConZonotope.Real.Operations.TightenPassER
public import CORALean.ContSet.ConZonotope.Real.Operations.TightenER
public import CORALean.ContSet.ConZonotope.Real.Operations.Eliminate
public import CORALean.ContSet.ConZonotope.Real.Operations.Project
public import CORALean.ContSet.ConZonotope.Real.Operations.ConstraintReduce
public import CORALean.ContSet.ConZonotope.Real.Operations.PartialSolveLamG
public import CORALean.ContSet.ConZonotope.Real.Operations.PartialSolveLamA
public import CORALean.ContSet.ConZonotope.Real.Operations.PartialSolve
public import CORALean.ContSet.ConZonotope.Real.Operations.Rescale
public import CORALean.ContSet.ConZonotope.Real.Operations.Lift
public import CORALean.ContSet.ConZonotope.Real.Operations.Empty
public import CORALean.ContSet.ConZonotope.Real.Operations.CartProd
public import CORALean.ContSet.ConZonotope.Real.Operations.Compact
public import CORALean.ContSet.ConZonotope.Real.Operations.CompactEmbed
public import CORALean.ContSet.ConZonotope.Real.Operations.CompactEqs
public import CORALean.ContSet.ConZonotope.Real.Operations.CompactGens
public import CORALean.ContSet.ConZonotope.Real.Operations.ConIntersect
public import CORALean.ContSet.ConZonotope.Real.Operations.Split
public import CORALean.ContSet.ConZonotope.Real.Operations.StripMat
public import CORALean.ContSet.ConZonotope.Real.Operations.IntersectStrip
public import CORALean.ContSet.ConZonotope.Real.Operations.IntersectStripFamily
public import CORALean.ContSet.ConZonotope.Real.Operations.IntersectMany
public import CORALean.ContSet.ConZonotope.Real.Operations.QuadMap
public import CORALean.ContSet.ConZonotope.Real.Operations.SupportBound
public import CORALean.ContSet.ConZonotope.Real.Operations.RepresentsaPoint
public import CORALean.ContSet.ConZonotope.Real.Operations.RepresentsaOrigin
public import CORALean.ContSet.ConZonotope.Real.Operations.RepresentsaEmptySet
public import CORALean.ContSet.ConZonotope.Real.Operations.ContainsPoint
public import CORALean.ContSet.ConZonotope.Real.Operations.IsCentre
public import CORALean.ContSet.ConZonotope.Real.Operations.Stack
public import CORALean.ContSet.ConZonotope.Real.Operations.NullPolytope
public import CORALean.ContSet.ConZonotope.Real.Operations.CubLinearAt
public import CORALean.ContSet.ConZonotope.Real.Operations.CubMap
public import CORALean.ContSet.ConZonotope.Real.Operations.CubMapMixed

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
