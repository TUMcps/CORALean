import CORALean.ContSet.Zonotope.Float.Theorems.MemGeneratorError
import CORALean.ContSet.Zonotope.Float.Theorems.PlusOuter
import CORALean.ContSet.Zonotope.Float.Theorems.LinCombOuter
import CORALean.ContSet.Zonotope.Float.Theorems.MtimesOuter
import CORALean.ContSet.Zonotope.Float.Theorems.IntervalOuter
import CORALean.ContSet.Zonotope.Float.Theorems.AbsorbErrorOuter
import CORALean.ContSet.Zonotope.Float.Theorems.ReduceByOuterRefines
import CORALean.ContSet.Zonotope.Float.Theorems.ReduceByOuter
import CORALean.ContSet.Zonotope.Float.Theorems.ReduceOuter
import CORALean.ContSet.Zonotope.Float.Theorems.ReduceAndAbsorbByOuter

/-!
# What `Zonotope` guarantees

Stated exactly as `Real` states it, over the same sets of real points and with
the same generator counts — rounding is paid into the error box, so no operation
but `absorbError` spends a generator on it.
-/
