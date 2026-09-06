import CORALean.ContSet.Zonotope.Float.Theorems.MemNominalSet
import CORALean.ContSet.Zonotope.Float.Theorems.MemGeneratorError
import CORALean.ContSet.Zonotope.Float.Theorems.PlusH
import CORALean.ContSet.Zonotope.Float.Theorems.PlusOuter
import CORALean.ContSet.Zonotope.Float.Theorems.LinCombH
import CORALean.ContSet.Zonotope.Float.Theorems.PairSumBracket
import CORALean.ContSet.Zonotope.Float.Theorems.PairDiffBracket
import CORALean.ContSet.Zonotope.Float.Theorems.SumPairMul
import CORALean.ContSet.Zonotope.Float.Theorems.MidpointMemResidual
import CORALean.ContSet.Zonotope.Float.Theorems.LinCombOuter
import CORALean.ContSet.Zonotope.Float.Theorems.MtimesH
import CORALean.ContSet.Zonotope.Float.Theorems.MtimesOuter
import CORALean.ContSet.Zonotope.Float.Theorems.AbsorbErrorH
import CORALean.ContSet.Zonotope.Float.Theorems.AbsSubMidLeErrorRadius
import CORALean.ContSet.Zonotope.Float.Theorems.ShiftBracketsMid
import CORALean.ContSet.Zonotope.Float.Theorems.AbsorbErrorOuter
import CORALean.ContSet.Zonotope.Float.Theorems.ReduceByOuterRefines
import CORALean.ContSet.Zonotope.Float.Theorems.ReduceByH
import CORALean.ContSet.Zonotope.Float.Theorems.AbsAbsorbedLeRadius
import CORALean.ContSet.Zonotope.Float.Theorems.ReduceByOuter
import CORALean.ContSet.Zonotope.Float.Theorems.ReduceGirardOuter
import CORALean.ContSet.Zonotope.Float.Theorems.ReduceCombastelOuter
import CORALean.ContSet.Zonotope.Float.Theorems.ReduceOuter
import CORALean.ContSet.Zonotope.Float.Theorems.ReduceOrder
import CORALean.ContSet.Zonotope.Float.Theorems.ReduceAndAbsorbByH
import CORALean.ContSet.Zonotope.Float.Theorems.ReduceAndAbsorbByOuter
import CORALean.ContSet.Zonotope.Float.Theorems.ReindexNominal
import CORALean.ContSet.Zonotope.Float.Theorems.ReindexExact

/-!
# What `Zonotope` guarantees

Stated exactly as `Real` states it, over the same sets of real points and with
the same generator counts — rounding is paid into the error box, so no operation
but `absorbError` spends a generator on it. `MemNominalSet` is what every one of
them reads the nominal half of a point in.
-/
