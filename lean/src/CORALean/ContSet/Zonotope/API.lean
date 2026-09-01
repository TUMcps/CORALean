import CORALean.ContSet.Zonotope.Real.API
import CORALean.ContSet.Zonotope.Float.API

/-!
# Zonotopes, both layers

`Real` is the specification, `Float` the refinement that pays its rounding into
an error box and proves the same `⊆`. `Float` imports `Real`, never the reverse.
-/
