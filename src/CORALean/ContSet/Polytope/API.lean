import CORALean.ContSet.Polytope.Polytope
import CORALean.ContSet.Polytope.VPolytope
import CORALean.ContSet.Polytope.Operations.API
import CORALean.ContSet.Polytope.Theorems.API
import CORALean.ContSet.Polytope.Instances

/-!
# Polytopes, collected

CORA's `polytope` is one class carrying either description and converting on
demand; here they are two, `Polytope` by halfspaces and `VPolytope` by vertices,
with no conversion between them. Vertex enumeration is a genuine algorithm and
would be its own development.

The specification only. A float layer would round the constraint bounds outward
and the vertices into a hull, neither of which any algorithm here needs yet.
-/
