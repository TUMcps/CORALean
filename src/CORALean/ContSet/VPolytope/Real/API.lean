import CORALean.ContSet.VPolytope.Real.VPolytope
import CORALean.ContSet.VPolytope.Real.Operations.API
import CORALean.ContSet.VPolytope.Real.Theorems.API
import CORALean.ContSet.VPolytope.Real.Instances

/-!
# Polytopes by vertices, collected

CORA's `polytope` with `isVRep` set. `HPolytope` is the same sets described by
halfspaces; the two are separate representations here, with no conversion
between them — converting either way is vertex enumeration, an algorithm in its
own right.

The specification only. A float layer would round the vertices outward into a
hull, which no algorithm here needs yet.
-/
