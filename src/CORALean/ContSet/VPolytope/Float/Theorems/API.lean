module

public import CORALean.ContSet.VPolytope.Float.Theorems.MatPolytopeExact
public import CORALean.ContSet.VPolytope.Float.Theorems.ProjectHighDimOuter
public import CORALean.ContSet.VPolytope.Float.Theorems.BoundDotLe
public import CORALean.ContSet.VPolytope.Float.Theorems.PlusOuter
public import CORALean.ContSet.VPolytope.Float.Theorems.MtimesOuter
public import CORALean.ContSet.VPolytope.Float.Theorems.NominalLinComb
public import CORALean.ContSet.VPolytope.Float.Theorems.LinCombOuter
public import CORALean.ContSet.VPolytope.Float.Theorems.IntersectionOuter
public import CORALean.ContSet.VPolytope.Float.Theorems.ProjectOuter
public import CORALean.ContSet.VPolytope.Float.Theorems.ConstructEmptySet
public import CORALean.ContSet.VPolytope.Float.Theorems.Convex
public import CORALean.ContSet.VPolytope.Float.Theorems.IsCompact
public import CORALean.ContSet.VPolytope.Float.Theorems.ConvHullOuter
public import CORALean.ContSet.VPolytope.Float.Theorems.EnclosePointsExact
public import CORALean.ContSet.VPolytope.Float.Theorems.OriginExact
public import CORALean.ContSet.VPolytope.Float.Theorems.CenterBoxMeets
public import CORALean.ContSet.VPolytope.Float.Theorems.IsFullDimSound

/-!
# What the float `VPolytope` guarantees

Each operation encloses what the exact one does. `plus` and `mtimes` go through
`construct_subset_add`, which is the only fact about vertex descriptions a float
layer needs: moving every vertex by something a convex box admits moves the hull
by no more.
-/
