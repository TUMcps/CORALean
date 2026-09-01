import CORALean.Global.API
import CORALean.Real.API
import CORALean.Float.API

/-!
# CORALean

`Real` is the specification: representations over ℝ, exact operations. `Float`
recomputes them with directed rounding and proves the same `⊆`.

The two are siblings on disk but not in the import graph — `Float` imports
`Real`, since a float operation is proved sound by composing the exact guarantee
with the direction the rounding went. Deleting `Float` leaves `Real` standing;
the reverse does not hold, and should not.
-/
