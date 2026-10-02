import CORALean.ContSet.ConZonotope.Float.Theorems.MemNominalSet
import CORALean.ContSet.ConZonotope.Float.Theorems.PlusOuter
import CORALean.ContSet.ConZonotope.Float.Theorems.LinCombOuter
import CORALean.ContSet.ConZonotope.Float.Theorems.ProjectOuter
import CORALean.ContSet.ConZonotope.Float.Theorems.ReduceOuter
import CORALean.ContSet.ConZonotope.Float.Theorems.UnionSubsetLinComb
import CORALean.ContSet.ConZonotope.Float.Theorems.ConvexHullSubsetLinComb
import CORALean.ContSet.ConZonotope.Float.Theorems.Convex
import CORALean.ContSet.ConZonotope.Float.Theorems.EmptyExact
import CORALean.ContSet.ConZonotope.Float.Theorems.IsCompact
import CORALean.ContSet.ConZonotope.Float.Theorems.OriginExact
import CORALean.ContSet.ConZonotope.Float.Theorems.MtimesOuter
import CORALean.ContSet.ConZonotope.Float.Theorems.ReindexExact

/-!
# What the float `ConZonotope` guarantees

Each operation encloses what the exact one does. The constraints cost nothing to
carry through `plus`, padding being exact, nor through `linComb`, where
weighting a row halves its right-hand side and halving is exact too; in both the
only rounding is the centre's, and the box absorbs it as a zonotope's does.
`MemNominalSet` is how each of them reads the nominal half of a point.
-/
