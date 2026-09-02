import CORALean.ContSet.HPolytope.Real.Operations.And
import CORALean.ContSet.HPolytope.Real.Operations.Box
import CORALean.ContSet.HPolytope.Real.Operations.Comap
import CORALean.ContSet.HPolytope.Real.Operations.MapEquiv
import CORALean.ContSet.HPolytope.Real.Operations.OfMat
import CORALean.ContSet.HPolytope.Real.Operations.Slab
import CORALean.ContSet.HPolytope.Real.Operations.Translate
import CORALean.ContSet.HPolytope.Real.Operations.UnitBox

/-!
# What `HPolytope` computes

The operations halfspaces are good at, all of them exact: intersection, which
concatenates the constraint lists; preimage, which precomposes them; the image
under an *invertible* map, which is the preimage under its inverse; and a
translation, which moves each bound by what its own constraint reads off the
shift.

What is missing needs an algorithm rather than a definition. Minkowski sum,
convex hull and the image under a general (non-invertible) map all go through
vertex enumeration, and the bounding box goes through `2n` linear programs. A
vertex description computes the first three directly, which is what `VPolytope`
is for.
-/
