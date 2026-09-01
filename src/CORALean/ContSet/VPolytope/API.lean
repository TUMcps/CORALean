import CORALean.ContSet.VPolytope.VPolytope
import CORALean.ContSet.VPolytope.Operations.API
import CORALean.ContSet.VPolytope.Theorems.API
import CORALean.ContSet.VPolytope.Instances

/-!
# Polytopes by vertices, collected

CORA's `polytope` with `isVRep` set. `HPolytope` is the same sets described by
halfspaces; the two are separate representations here, with no conversion
between them — converting either way is vertex enumeration, an algorithm in its
own right.

The specification only. A float layer would round the vertices outward into a
hull, which no algorithm here needs yet.
-/
