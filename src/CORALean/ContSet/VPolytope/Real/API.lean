module

public import CORALean.ContSet.VPolytope.Real.VPolytope
public import CORALean.ContSet.VPolytope.Real.Operations.API
public import CORALean.ContSet.VPolytope.Real.Theorems.API
public import CORALean.ContSet.VPolytope.Real.Counterexamples.API
public import CORALean.ContSet.VPolytope.Real.Complexity.API
public import CORALean.ContSet.VPolytope.Real.Instances
public import CORALean.ContSet.VPolytope.Real.Theorems.EncloseExact

/-!
# Polytopes by vertices, collected

CORA's `polytope` with `isVRep` set. `HPolytope` is the same sets described by
halfspaces; the two are separate representations here, converting either way
only by vertex enumeration, an algorithm in its own right.

The specification. `Float` pays its rounding into an error box rather than
into the vertices — a hull has no centre to move a rounded vertex away from.
-/
