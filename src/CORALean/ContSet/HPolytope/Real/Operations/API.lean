module

public import CORALean.ContSet.HPolytope.Real.Operations.Intersection
public import CORALean.ContSet.HPolytope.Real.Operations.TightAt
public import CORALean.ContSet.HPolytope.Real.Operations.BasicPoint
public import CORALean.ContSet.HPolytope.Real.Operations.Comap
public import CORALean.ContSet.HPolytope.Real.Operations.Basic
public import CORALean.ContSet.HPolytope.Real.Operations.BoundOfDual
public import CORALean.ContSet.HPolytope.Real.Operations.EmptySet
public import CORALean.ContSet.HPolytope.Real.Operations.Fullspace
public import CORALean.ContSet.HPolytope.Real.Operations.LinComb
public import CORALean.ContSet.HPolytope.Real.Operations.MapEquiv
public import CORALean.ContSet.HPolytope.Real.Operations.Mtimes
public import CORALean.ContSet.HPolytope.Real.Operations.OfBounds
public import CORALean.ContSet.HPolytope.Real.Operations.OfBoundsOpt
public import CORALean.ContSet.HPolytope.Real.Operations.Rows
public import CORALean.ContSet.HPolytope.Real.Operations.RowLin
public import CORALean.ContSet.HPolytope.Real.Operations.Ineqs
public import CORALean.ContSet.HPolytope.Real.Operations.Eqs
public import CORALean.ContSet.HPolytope.Real.Operations.Plus
public import CORALean.ContSet.HPolytope.Real.Operations.MinkDiffOf
public import CORALean.ContSet.HPolytope.Real.Operations.Slab
public import CORALean.ContSet.HPolytope.Real.Operations.Translate
public import CORALean.ContSet.HPolytope.Real.Operations.UnitBox
public import CORALean.ContSet.HPolytope.Real.Operations.HalfScaled
public import CORALean.ContSet.HPolytope.Real.Operations.OfPoint
public import CORALean.ContSet.HPolytope.Real.Operations.SupportBound
public import CORALean.ContSet.HPolytope.Real.Operations.Stack
public import CORALean.ContSet.HPolytope.Real.Operations.Lift
public import CORALean.ContSet.HPolytope.Real.Operations.OfEqs1D
public import CORALean.ContSet.HPolytope.Real.Operations.ZonoBundleVar
public import CORALean.ContSet.HPolytope.Real.Operations.NormalizeConstraints
public import CORALean.ContSet.HPolytope.Real.Operations.NormalizeRows
public import CORALean.ContSet.HPolytope.Real.Operations.ProjectHighDim
public import CORALean.ContSet.HPolytope.Real.Operations.ReduceOverDomain
public import CORALean.ContSet.HPolytope.Real.Operations.AffineHullBasis
public import CORALean.ContSet.HPolytope.Real.Operations.GenerateRandomH
public import CORALean.ContSet.HPolytope.Real.Operations.IsequalNondeg
public import CORALean.ContSet.HPolytope.Real.Operations.SimplexRows
public import CORALean.ContSet.HPolytope.Real.Operations.Restrict
public import CORALean.ContSet.HPolytope.Real.Operations.CompactZeros
public import CORALean.ContSet.HPolytope.Real.Operations.CompactAlignedIneq
public import CORALean.ContSet.HPolytope.Real.Operations.CompactAtoAe
public import CORALean.ContSet.HPolytope.Real.Operations.RepresentsaFullspace
public import CORALean.ContSet.HPolytope.Real.Operations.IsLPCenter
public import CORALean.ContSet.HPolytope.Real.Operations.Volume
public import CORALean.ContSet.HPolytope.Real.Operations.RowsRhs
public import CORALean.ContSet.HPolytope.Real.Operations.ToIneqs
public import CORALean.ContSet.HPolytope.Real.Operations.RowNorm
public import CORALean.ContSet.HPolytope.Real.Operations.HitTime
public import CORALean.ContSet.HPolytope.Real.Operations.ChordHighIndex
public import CORALean.ContSet.HPolytope.Real.Operations.ChordLowIndex
public import CORALean.ContSet.HPolytope.Real.Operations.ChordHigh
public import CORALean.ContSet.HPolytope.Real.Operations.ChordLow
public import CORALean.ContSet.HPolytope.Real.Operations.HitAndRunStep
public import CORALean.ContSet.HPolytope.Real.Operations.FacetNormal
public import CORALean.ContSet.HPolytope.Real.Operations.BilliardEnd
public import CORALean.ContSet.HPolytope.Real.Operations.BilliardStep

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
