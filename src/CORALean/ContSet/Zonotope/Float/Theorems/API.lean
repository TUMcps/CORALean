import CORALean.ContSet.Zonotope.Float.Theorems.MemNominalSet
import CORALean.ContSet.Zonotope.Float.Theorems.MemGeneratorError
import CORALean.ContSet.Zonotope.Float.Theorems.PlusOuter
import CORALean.ContSet.Zonotope.Float.Theorems.LinCombOuter
import CORALean.ContSet.Zonotope.Float.Theorems.MtimesOuter
import CORALean.ContSet.Zonotope.Float.Theorems.AbsorbErrorOuter
import CORALean.ContSet.Zonotope.Float.Theorems.ReduceByOuterRefines
import CORALean.ContSet.Zonotope.Float.Theorems.ReduceByOuter
import CORALean.ContSet.Zonotope.Float.Theorems.ReduceOuter
import CORALean.ContSet.Zonotope.Float.Theorems.ReduceOrder
import CORALean.ContSet.Zonotope.Float.Theorems.ReduceAndAbsorbByOuter
import CORALean.ContSet.Zonotope.Float.Theorems.ReindexExact

/-!
# What `Zonotope` guarantees

Stated exactly as `Real` states it, over the same sets of real points and with
the same generator counts — rounding is paid into the error box, so no operation
but `absorbError` spends a generator on it. `MemNominalSet` is what every one of
them reads the nominal half of a point in.
-/
