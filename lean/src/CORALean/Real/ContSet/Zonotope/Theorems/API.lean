import CORALean.Real.ContSet.Zonotope.Theorems.Coefficient
import CORALean.Real.ContSet.Zonotope.Theorems.PlusExact
import CORALean.Real.ContSet.Zonotope.Theorems.MtimesExact
import CORALean.Real.ContSet.Zonotope.Theorems.IntervalOuter
import CORALean.Real.ContSet.Zonotope.Theorems.Convex
import CORALean.Real.ContSet.Zonotope.Theorems.IsBounded
import CORALean.Real.ContSet.Zonotope.Theorems.IsCompact
import CORALean.Real.ContSet.Zonotope.Theorems.LinCombOuter
import CORALean.Real.ContSet.Zonotope.Theorems.MtimesIntervalMatOuter
import CORALean.Real.ContSet.Zonotope.Theorems.ReduceOuter

/-!
# What `Zonotope` guarantees

One file per guarantee, named after the theorem it states. Auxiliary lemmas a
proof needs carry the `aux_` prefix and are used nowhere else; `Coefficient`
holds the shared devices, which the float layer needs too.
-/
