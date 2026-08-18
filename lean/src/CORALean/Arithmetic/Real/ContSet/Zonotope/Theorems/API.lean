import CORALean.Arithmetic.Real.ContSet.Zonotope.Theorems.Coefficient
import CORALean.Arithmetic.Real.ContSet.Zonotope.Theorems.PlusExact
import CORALean.Arithmetic.Real.ContSet.Zonotope.Theorems.MtimesExact
import CORALean.Arithmetic.Real.ContSet.Zonotope.Theorems.IntervalOuter
import CORALean.Arithmetic.Real.ContSet.Zonotope.Theorems.ReduceOuter

/-!
# What `Zonotope` guarantees

One file per guarantee, named after the theorem it states. Auxiliary lemmas a
proof needs carry the `aux_` prefix and are used nowhere else; `Coefficient`
holds the shared devices, which the float layer needs too.
-/
