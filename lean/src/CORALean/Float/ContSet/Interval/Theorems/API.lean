import CORALean.Float.ContSet.Interval.Theorems.PlusOuter
import CORALean.Float.ContSet.Interval.Theorems.LinCombOuter
import CORALean.Float.ContSet.Interval.Theorems.MtimesOuter
import CORALean.Float.ContSet.Interval.Theorems.SubMemResidual

/-!
# What `Interval` guarantees

Stated exactly as `Real` states it — the same `⊆`, over the same sets
of real points — and proved the same way each time: the exact guarantee composed
with the refinement, which is the `aux_` lemma beside it. No set-level reasoning
is repeated here.
-/
