import CORALean.ContSet.VPolytope.Real.VPolytope
import CORALean.ContSet.VPolytope.Real.Operations.API
import CORALean.ContSet.VPolytope.Real.Theorems.API
import CORALean.ContSet.VPolytope.Real.Complexity.API
import CORALean.ContSet.VPolytope.Real.Cost.API
import CORALean.ContSet.VPolytope.Real.Instances
import CORALean.ContSet.VPolytope.Real.Theorems.EncloseExact

/-!
# Polytopes by vertices, collected

CORA's `polytope` with `isVRep` set. `HPolytope` is the same sets described by
halfspaces; the two are separate representations here, converting either way
only by vertex enumeration, an algorithm in its own right.

The specification. `Float` pays its rounding into an error box rather than
into the vertices — a hull has no centre to move a rounded vertex away from.
-/
