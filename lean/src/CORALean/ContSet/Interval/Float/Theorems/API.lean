import CORALean.ContSet.Interval.Float.Theorems.PlusOuter
import CORALean.ContSet.Interval.Float.Theorems.LinCombOuter
import CORALean.ContSet.Interval.Float.Theorems.MtimesOuter
import CORALean.ContSet.Interval.Float.Theorems.SubMemResidual

/-!
# What `Interval` guarantees

Stated exactly as `Real` states it — the same `⊆`, over the same sets
of real points — and proved the same way each time: the exact guarantee composed
with the refinement, which is the `aux_` lemma beside it. No set-level reasoning
is repeated here.
-/
