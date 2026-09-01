import CORALean.Global.API
import CORALean.Global.Float.API
import CORALean.ContSet.API
import CORALean.ContDynamics.API

/-!
# CORALean

A representation present in both arithmetic layers holds one directory per
layer: `Real` is the specification, exact over ℝ, and `Float` recomputes it with
directed rounding and proves the same `⊆`. One present in a single layer stays
flat, and its namespace says which.

The two layers are siblings on disk but not in the import graph — `Float`
imports `Real`, since a float operation is proved sound by composing the exact
guarantee with the direction the rounding went. Deleting every `Float`
directory leaves the specification standing; the reverse does not hold, and
should not.
-/
