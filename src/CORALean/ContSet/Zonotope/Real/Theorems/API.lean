import CORALean.ContSet.Zonotope.Real.Theorems.Coefficient
import CORALean.ContSet.Zonotope.Real.Theorems.PlusExact
import CORALean.ContSet.Zonotope.Real.Theorems.MapExact
import CORALean.ContSet.Zonotope.Real.Theorems.IntervalOuter
import CORALean.ContSet.Zonotope.Real.Theorems.Convex
import CORALean.ContSet.Zonotope.Real.Theorems.IsBounded
import CORALean.ContSet.Zonotope.Real.Theorems.IsCompact
import CORALean.ContSet.Zonotope.Real.Theorems.LinCombOuter
import CORALean.ContSet.Zonotope.Real.Theorems.MtimesIntervalMatOuter
import CORALean.ContSet.Zonotope.Real.Theorems.ReduceOuter

/-!
# What `Zonotope` guarantees

`plus` and `map` exactly, `reduce` and the interval hull as enclosures, and the
topological facts a set-valued integral needs. `Coefficient` holds the shared
proof devices, which the float layer needs too.
-/
