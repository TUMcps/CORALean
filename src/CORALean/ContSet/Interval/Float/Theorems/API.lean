import CORALean.ContSet.Interval.Float.Theorems.PlusOuter
import CORALean.ContSet.Interval.Float.Theorems.LinCombOuter
import CORALean.ContSet.Interval.Float.Theorems.MtimesOuter
import CORALean.ContSet.Interval.Float.Theorems.SubMemResidual
import CORALean.ContSet.Interval.Float.Theorems.ReindexNominal
import CORALean.ContSet.Interval.Float.Theorems.ReindexExact

/-!
# What `Interval` guarantees

Stated exactly as `Real` states it, over the same sets of real points, and proved
the same way each time: the exact guarantee composed with the `aux_..._refines`
lemma beside it. No set-level reasoning is repeated here.
-/
