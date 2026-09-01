import CORALean.ContSet.Interval.Real.API
import CORALean.ContSet.Interval.Float.API

/-!
# Intervals, both layers

`Real` is the specification, `Float` the refinement that rounds outward and
proves the same `⊆`. `Float` imports `Real`, never the reverse.
-/
