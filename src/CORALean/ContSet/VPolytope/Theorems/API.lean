import CORALean.ContSet.VPolytope.Theorems.Convex
import CORALean.ContSet.VPolytope.Theorems.ConvexHull
import CORALean.ContSet.VPolytope.Theorems.IsCompact
import CORALean.ContSet.VPolytope.Theorems.PlusExact
import CORALean.ContSet.VPolytope.Theorems.MapExact
import CORALean.ContSet.VPolytope.Theorems.LinCombOuter

/-!
# What `VPolytope` guarantees

`ConvexHull` is the pivot: once a vertex list is known to denote the hull of its
range, every other guarantee is hull algebra applied to `Set.range V`.
-/
