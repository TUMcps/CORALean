module

public import CORALean.ContSet.VPolytope.Float.VPolytope
public import CORALean.ContSet.VPolytope.Float.Operations.API
public import CORALean.ContSet.VPolytope.Float.Theorems.API
public import CORALean.ContSet.VPolytope.Float.Instances

/-!
# Vertex descriptions over a floating-point scalar, collected

The rounding goes into an error box rather than into the vertices, since a hull
has no centre to move a vertex away from.
-/
