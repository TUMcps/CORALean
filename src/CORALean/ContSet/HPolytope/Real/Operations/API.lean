import CORALean.ContSet.HPolytope.Real.Operations.And
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
import CORALean.ContSet.HPolytope.Real.Operations.UnitBox
import CORALean.ContSet.HPolytope.Real.Operations.MemUnitBoxIff
import CORALean.ContSet.HPolytope.Real.Operations.HalfScaled
import CORALean.ContSet.HPolytope.Real.Operations.MemHalfScaledIff
import CORALean.ContSet.HPolytope.Real.Operations.MemHalfScaledComap
import CORALean.ContSet.HPolytope.Real.Operations.RowsOfMemHalfScaledComap
import CORALean.ContSet.HPolytope.Real.Operations.AbsLeOfUnitBoxRows
import CORALean.ContSet.HPolytope.Real.Operations.OfPoint

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
is the shape they share, `BoundOfDual` where a halfspace description's own
certificates come from. Soundness never depends on the directions, only
precision does, so enumerating the true facets stays outside as an optimisation.

`Fullspace` and `EmptySet` are the unit and the absorbing element of the first
group, each written out as the rows that denote it. `minkDiffOf` is exact too:
each row shifts inward by the subtrahend's support, taken in rather than
computed, as `mtimesOf` also takes what it cannot compute — `ofPoint` costs `n`
equality rows, not zero generators, the one representation a point isn't free for.
-/
