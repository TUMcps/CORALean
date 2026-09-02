import CORALean.ContSet.VPolytope.Real.Theorems.Convex
import CORALean.ContSet.VPolytope.Real.Theorems.ConvexHull
import CORALean.ContSet.VPolytope.Real.Theorems.IsCompact
import CORALean.ContSet.VPolytope.Real.Theorems.PlusExact
import CORALean.ContSet.VPolytope.Real.Theorems.MapExact
import CORALean.ContSet.VPolytope.Real.Theorems.LinCombOuter

/-!
# What `VPolytope` guarantees

`ConvexHull` is the pivot: once a vertex list is known to denote the hull of its
range, every other guarantee is hull algebra applied to `Set.range V`.
-/
