import CORALean.ContSet.VPolytope.Float.Theorems.BoundDotLe
import CORALean.ContSet.VPolytope.Float.Theorems.PlusOuter
import CORALean.ContSet.VPolytope.Float.Theorems.MtimesOuter
import CORALean.ContSet.VPolytope.Float.Theorems.NominalLinComb
import CORALean.ContSet.VPolytope.Float.Theorems.LinCombOuter
import CORALean.ContSet.VPolytope.Float.Theorems.IntersectionOuter
import CORALean.ContSet.VPolytope.Float.Theorems.ProjectOuter

/-!
# What the float `VPolytope` guarantees

Each operation encloses what the exact one does. `plus` and `mtimes` go through
`construct_subset_add`, which is the only fact about vertex descriptions a float
layer needs: moving every vertex by something a convex box admits moves the hull
by no more.
-/
