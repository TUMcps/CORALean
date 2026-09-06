import CORALean.ContSet.VPolytope.Real.Theorems.VertexMem
import CORALean.ContSet.VPolytope.Real.Theorems.AndOuter
import CORALean.ContSet.VPolytope.Real.Theorems.Convex
import CORALean.ContSet.VPolytope.Real.Theorems.ConvexHull
import CORALean.ContSet.VPolytope.Real.Theorems.IsCompact
import CORALean.ContSet.VPolytope.Real.Theorems.IsClosed
import CORALean.ContSet.VPolytope.Real.Theorems.IsBounded
import CORALean.ContSet.VPolytope.Real.Theorems.LinCombOuter
import CORALean.ContSet.VPolytope.Real.Theorems.MapExact
import CORALean.ContSet.VPolytope.Real.Theorems.MtimesExact
import CORALean.ContSet.VPolytope.Real.Theorems.BilinOuter
import CORALean.ContSet.VPolytope.Real.Theorems.MtimesMatPolytopeOuter
import CORALean.ContSet.VPolytope.Real.Theorems.PlusExact

/-!
# What `VPolytope` guarantees

`ConvexHull` is the pivot: once a vertex list is known to denote the hull of its
range, every other guarantee is hull algebra applied to `Set.range V`, and
`VertexMem` is the inclusion that gets it there.

`bilin_outer` is the one guarantee that is an outer inclusion rather than an
equality: not because anything is lost, but because the convex-hull equality
behind it is not proved here. `mtimesMatPolytope_outer` reads it back at `*ᵥ`.
-/
