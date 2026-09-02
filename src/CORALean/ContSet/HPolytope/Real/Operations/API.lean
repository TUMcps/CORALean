import CORALean.ContSet.HPolytope.Real.Operations.And
import CORALean.ContSet.HPolytope.Real.Operations.BasicPoint
import CORALean.ContSet.HPolytope.Real.Operations.Comap
import CORALean.ContSet.HPolytope.Real.Operations.DualBound
import CORALean.ContSet.HPolytope.Real.Operations.LinComb
import CORALean.ContSet.HPolytope.Real.Operations.MapEquiv
import CORALean.ContSet.HPolytope.Real.Operations.Mtimes
import CORALean.ContSet.HPolytope.Real.Operations.OfBounds
import CORALean.ContSet.HPolytope.Real.Operations.OfMat
import CORALean.ContSet.HPolytope.Real.Operations.Plus
import CORALean.ContSet.HPolytope.Real.Operations.Slab
import CORALean.ContSet.HPolytope.Real.Operations.Translate
import CORALean.ContSet.HPolytope.Real.Operations.UnitBox

/-!
# What `HPolytope` computes

Two groups, and which one an operation is in is decided by whether the answer's
rows are determined by the inputs' rows.

Exact, because they are: intersection concatenates the constraint lists,
preimage precomposes them, the image under an *invertible* map is the preimage
under its inverse, a translation moves each bound by what its own constraint
reads off the shift, and a box is `2n` rows written out.

Enclosing, because they are not: Minkowski sum, `linComb`, the image under a
general map, and the bounding box all produce rows nobody named, so the caller
names directions instead and each bound comes from a certificate —
`ofBounds` is the shape they share, `DualBound` where a halfspace description's
own certificates come from. Soundness never depends on the directions, only
precision does, so enumerating the true facets stays outside as an optimisation.
-/
