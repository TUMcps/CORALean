import CORALean.ContSet.PolyZonotope.Real.Theorems.PlusExact
import CORALean.ContSet.PolyZonotope.Real.Theorems.MapExact
import CORALean.ContSet.PolyZonotope.Real.Theorems.LinCombOuter
import CORALean.ContSet.PolyZonotope.Real.Theorems.DependentExact
import CORALean.ContSet.PolyZonotope.Real.Theorems.QuadMapExact

/-!
# What `PolyZonotope` guarantees

`plus`, `map`, `dependent` and `quadMap` exactly; `linComb` as an enclosure, and
the module docstring there says which coefficients cost the other direction.

`quadMap_exact` is the one that distinguishes the representation: no convex
representation here can state it.
-/
