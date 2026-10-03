import CORALean.ContSet.VPolytope.Float.Theorems.ProjectHighDimOuter
import CORALean.ContSet.VPolytope.Float.Theorems.BoundDotLe
import CORALean.ContSet.VPolytope.Float.Theorems.PlusOuter
import CORALean.ContSet.VPolytope.Float.Theorems.MtimesOuter
import CORALean.ContSet.VPolytope.Float.Theorems.NominalLinComb
import CORALean.ContSet.VPolytope.Float.Theorems.LinCombOuter
import CORALean.ContSet.VPolytope.Float.Theorems.IntersectionOuter
import CORALean.ContSet.VPolytope.Float.Theorems.ProjectOuter
import CORALean.ContSet.VPolytope.Float.Theorems.ConstructEmptySet
import CORALean.ContSet.VPolytope.Float.Theorems.Convex
import CORALean.ContSet.VPolytope.Float.Theorems.IsCompact
import CORALean.ContSet.VPolytope.Float.Theorems.ConvHullOuter
import CORALean.ContSet.VPolytope.Float.Theorems.EnclosePointsExact
import CORALean.ContSet.VPolytope.Float.Theorems.OriginExact

/-!
# What the float `VPolytope` guarantees

Each operation encloses what the exact one does. `plus` and `mtimes` go through
`construct_subset_add`, which is the only fact about vertex descriptions a float
layer needs: moving every vertex by something a convex box admits moves the hull
by no more.
-/
