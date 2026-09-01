import CORALean.ContSet.Polytope.Theorems.Convex
import CORALean.ContSet.Polytope.Theorems.ConvexHull
import CORALean.ContSet.Polytope.Theorems.AndExact
import CORALean.ContSet.Polytope.Theorems.ComapExact
import CORALean.ContSet.Polytope.Theorems.IsClosed
import CORALean.ContSet.Polytope.Theorems.IsCompact
import CORALean.ContSet.Polytope.Theorems.PlusExact
import CORALean.ContSet.Polytope.Theorems.MapExact
import CORALean.ContSet.Polytope.Theorems.LinCombOuter

/-!
# What the two polytope representations guarantee

Every operation is exact, neither representation being an approximation of
anything — the loss is in what each one cannot compute at all.

`ConvexHull` is the pivot: once a vertex description is known to denote the hull
of its vertices, its remaining guarantees are hull algebra.
-/
