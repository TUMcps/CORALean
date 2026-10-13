import CORALean.ContSet.HPolytope.Real.Operations.Intersection
import CORALean.ContSet.HPolytope.Real.Operations.TightAt
import CORALean.ContSet.HPolytope.Real.Operations.BasicPoint
import CORALean.ContSet.HPolytope.Real.Operations.BasicPointTightAt
import CORALean.ContSet.HPolytope.Real.Operations.Comap
import CORALean.ContSet.HPolytope.Real.Operations.ConstructEqFeasible
import CORALean.ContSet.HPolytope.Real.Operations.BoundOfDual
import CORALean.ContSet.HPolytope.Real.Operations.ConstructEqEmptyOfDual
import CORALean.ContSet.HPolytope.Real.Operations.EmptySet
import CORALean.ContSet.HPolytope.Real.Operations.ConstructEmptySet
import CORALean.ContSet.HPolytope.Real.Operations.Fullspace
import CORALean.ContSet.HPolytope.Real.Operations.ConstructFullspace
import CORALean.ContSet.HPolytope.Real.Operations.LinComb
import CORALean.ContSet.HPolytope.Real.Operations.MapEquiv
import CORALean.ContSet.HPolytope.Real.Operations.Mtimes
import CORALean.ContSet.HPolytope.Real.Operations.OfBounds
import CORALean.ContSet.HPolytope.Real.Operations.SubsetOfBounds
import CORALean.ContSet.HPolytope.Real.Operations.OfBoundsOpt
import CORALean.ContSet.HPolytope.Real.Operations.SubsetOfBoundsOpt
import CORALean.ContSet.HPolytope.Real.Operations.Rows
import CORALean.ContSet.HPolytope.Real.Operations.RowLin
import CORALean.ContSet.HPolytope.Real.Operations.Ineqs
import CORALean.ContSet.HPolytope.Real.Operations.Eqs
import CORALean.ContSet.HPolytope.Real.Operations.MemIneqsIff
import CORALean.ContSet.HPolytope.Real.Operations.MemEqsIff
import CORALean.ContSet.HPolytope.Real.Operations.Plus
import CORALean.ContSet.HPolytope.Real.Operations.MinkDiffOf
import CORALean.ContSet.HPolytope.Real.Operations.Slab
import CORALean.ContSet.HPolytope.Real.Operations.MemSlabIff
import CORALean.ContSet.HPolytope.Real.Operations.MemSlabSelfIff
import CORALean.ContSet.HPolytope.Real.Operations.Translate
import CORALean.ContSet.HPolytope.Real.Operations.Minus
import CORALean.ContSet.HPolytope.Real.Operations.UnitBox
import CORALean.ContSet.HPolytope.Real.Operations.MemUnitBoxIff
import CORALean.ContSet.HPolytope.Real.Operations.HalfScaled
import CORALean.ContSet.HPolytope.Real.Operations.MemHalfScaledIff
import CORALean.ContSet.HPolytope.Real.Operations.MemHalfScaledComap
import CORALean.ContSet.HPolytope.Real.Operations.RowsOfMemHalfScaledComap
import CORALean.ContSet.HPolytope.Real.Operations.AbsLeOfUnitBoxRows
import CORALean.ContSet.HPolytope.Real.Operations.OfPoint
import CORALean.ContSet.HPolytope.Real.Operations.SupportBound
import CORALean.ContSet.HPolytope.Real.Operations.Stack
import CORALean.ContSet.HPolytope.Real.Operations.Lift
import CORALean.ContSet.HPolytope.Real.Operations.MldivideCora
import CORALean.ContSet.HPolytope.Real.Operations.ConvHullCora
import CORALean.ContSet.HPolytope.Real.Operations.OfEqs1D
import CORALean.ContSet.HPolytope.Real.Operations.MinkDiff1DCora
import CORALean.ContSet.HPolytope.Real.Operations.Compact1DEqCora
import CORALean.ContSet.HPolytope.Real.Operations.IsIntersectingVPolyCora
import CORALean.ContSet.HPolytope.Real.Operations.RepresentsaIntervalCora
import CORALean.ContSet.HPolytope.Real.Operations.NormalizeConstraints
import CORALean.ContSet.HPolytope.Real.Operations.NormalizeRows
import CORALean.ContSet.HPolytope.Real.Operations.ProjectHighDim
import CORALean.ContSet.HPolytope.Real.Operations.ReduceOverDomain
import CORALean.ContSet.HPolytope.Real.Operations.AffineHullBasis
import CORALean.ContSet.HPolytope.Real.Operations.GenerateRandomH
import CORALean.ContSet.HPolytope.Real.Operations.IsequalNondeg
import CORALean.ContSet.HPolytope.Real.Operations.SimplexRows
import CORALean.ContSet.HPolytope.Real.Operations.Restrict
import CORALean.ContSet.HPolytope.Real.Operations.CompactZeros
import CORALean.ContSet.HPolytope.Real.Operations.CompactAlignedIneq
import CORALean.ContSet.HPolytope.Real.Operations.MoveToEq
import CORALean.ContSet.HPolytope.Real.Operations.AtoAeState
import CORALean.ContSet.HPolytope.Real.Operations.CompactAtoAe
import CORALean.ContSet.HPolytope.Real.Operations.RepresentsaFullspace
import CORALean.ContSet.HPolytope.Real.Operations.IsLPCentre
import CORALean.ContSet.HPolytope.Real.Operations.Volume
import CORALean.ContSet.HPolytope.Real.Operations.RowsRhs
import CORALean.ContSet.HPolytope.Real.Operations.RowNorm

import CORALean.ContSet.HPolytope.Real.Operations.HitTime
import CORALean.ContSet.HPolytope.Real.Operations.ChordHighIndex
import CORALean.ContSet.HPolytope.Real.Operations.ChordLowIndex
import CORALean.ContSet.HPolytope.Real.Operations.ChordHigh
import CORALean.ContSet.HPolytope.Real.Operations.ChordLow
import CORALean.ContSet.HPolytope.Real.Operations.HitAndRunStep
import CORALean.ContSet.HPolytope.Real.Operations.FacetNormal
import CORALean.ContSet.HPolytope.Real.Operations.BilliardEnd
import CORALean.ContSet.HPolytope.Real.Operations.BilliardStep
/-!
# What `HPolytope` computes

Two groups, and which one an operation is in is decided by whether the answer's
rows are determined by the inputs' rows.

Exact, because they are: intersection concatenates the constraint lists,
preimage precomposes them, the image under an *invertible* map is the preimage
under its inverse, a translation moves each bound by what its own constraint
reads off the shift, a weighted copy halves every right-hand side into the
constraint that reads the weight, and a box is `2n` rows written out.

Enclosing, because they are not: Minkowski sum, `linComb`, the image under a
general map, and the bounding box all produce rows nobody named, so the caller
names directions instead and each bound comes from a certificate — `ofBounds`
is the shape they share, `BoundOfDual` and `SupportBound` where a halfspace
description's own certificates come from, the latter by simplex and a check.
Soundness never depends on the directions, only precision does.

`Fullspace` and `EmptySet` are the unit and the absorbing element of the first
group, each written out as the rows that denote it. `minkDiffOf` is exact too:
each row shifts inward by the subtrahend's support, taken in rather than
computed, as `mtimesOf` also takes what it cannot compute — `ofPoint` costs `n`
equality rows, not zero generators, the one representation a point isn't free for.
-/
