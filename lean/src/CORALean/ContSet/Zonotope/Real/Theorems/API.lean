import CORALean.ContSet.Zonotope.Real.Theorems.Coefficient
import CORALean.ContSet.Zonotope.Real.Theorems.PlusExact
import CORALean.ContSet.Zonotope.Real.Theorems.MtimesExact
import CORALean.ContSet.Zonotope.Real.Theorems.IntervalOuter
import CORALean.ContSet.Zonotope.Real.Theorems.Convex
import CORALean.ContSet.Zonotope.Real.Theorems.IsBounded
import CORALean.ContSet.Zonotope.Real.Theorems.IsCompact
import CORALean.ContSet.Zonotope.Real.Theorems.LinCombOuter
import CORALean.ContSet.Zonotope.Real.Theorems.MtimesIntervalMatOuter
import CORALean.ContSet.Zonotope.Real.Theorems.ReduceOuter

/-!
# What `Zonotope` guarantees

One file per guarantee, named after the theorem it states. Auxiliary lemmas a
proof needs carry the `aux_` prefix and are used nowhere else; `Coefficient`
holds the shared devices, which the float layer needs too.
-/
