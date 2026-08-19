import CORALean.Arithmetic.Float.ContSet.Interval.Theorems.PlusOuter
import CORALean.Arithmetic.Float.ContSet.Interval.Theorems.LinCombOuter
import CORALean.Arithmetic.Float.ContSet.Interval.Theorems.MtimesOuter
import CORALean.Arithmetic.Float.ContSet.Interval.Theorems.SubMemResidual

/-!
# What `Interval` guarantees

Stated exactly as `Arithmetic.Real` states it — the same `⊆`, over the same sets
of real points — and proved the same way each time: the exact guarantee composed
with the refinement, which is the `aux_` lemma beside it. No set-level reasoning
is repeated here.
-/
