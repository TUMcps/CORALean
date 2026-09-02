import CORALean.ContSet.VPolytope.Float.Theorems.PlusOuter
import CORALean.ContSet.VPolytope.Float.Theorems.MtimesOuter
import CORALean.ContSet.VPolytope.Float.Theorems.LinCombOuter
import CORALean.ContSet.VPolytope.Float.Theorems.IntervalOuter
import CORALean.ContSet.VPolytope.Float.Theorems.AndOuter

/-!
# What the float `VPolytope` guarantees

Each operation encloses what the exact one does. `plus` and `mtimes` go through
`construct_subset_add`, which is the only fact about vertex descriptions a float
layer needs: moving every vertex by something a convex box admits moves the hull
by no more.
-/
