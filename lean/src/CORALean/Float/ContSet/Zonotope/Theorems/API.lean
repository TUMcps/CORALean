import CORALean.Float.ContSet.Zonotope.Theorems.MemGeneratorError
import CORALean.Float.ContSet.Zonotope.Theorems.PlusOuter
import CORALean.Float.ContSet.Zonotope.Theorems.LinCombOuter
import CORALean.Float.ContSet.Zonotope.Theorems.MtimesOuter
import CORALean.Float.ContSet.Zonotope.Theorems.IntervalOuter
import CORALean.Float.ContSet.Zonotope.Theorems.AbsorbErrorOuter
import CORALean.Float.ContSet.Zonotope.Theorems.ReduceByOuterRefines
import CORALean.Float.ContSet.Zonotope.Theorems.ReduceByOuter
import CORALean.Float.ContSet.Zonotope.Theorems.ReduceOuter
import CORALean.Float.ContSet.Zonotope.Theorems.ReduceAndAbsorbByOuter

/-!
# What `Zonotope` guarantees

Stated exactly as `Real` states it, over the same sets of real points
and with the same generator counts. One file per guarantee; auxiliary lemmas a
proof needs carry the `aux_` prefix and are used nowhere else.
-/
