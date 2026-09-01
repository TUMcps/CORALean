import CORALean.ContSet.HPolytope.Operations.And
import CORALean.ContSet.HPolytope.Operations.Comap
import CORALean.ContSet.HPolytope.Operations.OfMat
import CORALean.ContSet.HPolytope.Operations.UnitBox

/-!
# What `HPolytope` computes

The operations halfspaces are good at: intersection, which concatenates the
constraint lists, and preimage, which precomposes them. Both exact. The ones a
vertex description is good at — Minkowski sum, image, convex hull — would need
vertex enumeration first and are not here.
-/
