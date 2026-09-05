import CORALean.ContSet.ConPolyZono.Float.Operations.AgreeRow
import CORALean.ContSet.ConPolyZono.Float.Operations.AndA
import CORALean.ContSet.ConPolyZono.Float.Operations.AndAgree
import CORALean.ContSet.ConPolyZono.Float.Operations.AndB
import CORALean.ContSet.ConPolyZono.Float.Operations.AndDep
import CORALean.ContSet.ConPolyZono.Float.Operations.And
import CORALean.ContSet.ConPolyZono.Float.Operations.MergedCol
import CORALean.ContSet.ConPolyZono.Float.Operations.MergedColUp
import CORALean.ContSet.ConPolyZono.Float.Operations.CompactGensGap
import CORALean.ContSet.ConPolyZono.Float.Operations.CompactGens
import CORALean.ContSet.ConPolyZono.Float.Operations.MergedConsCol
import CORALean.ContSet.ConPolyZono.Float.Operations.MergedConsColUp
import CORALean.ContSet.ConPolyZono.Float.Operations.CompactConsGap
import CORALean.ContSet.ConPolyZono.Float.Operations.CompactConsB
import CORALean.ContSet.ConPolyZono.Float.Operations.CompactCons
import CORALean.ContSet.ConPolyZono.Float.Operations.CompactFactors
import CORALean.ContSet.ConPolyZono.Float.Operations.Compact
import CORALean.ContSet.ConPolyZono.Float.Operations.Dependent
import CORALean.ContSet.ConPolyZono.Float.Operations.PlusA
import CORALean.ContSet.ConPolyZono.Float.Operations.PlusB
import CORALean.ContSet.ConPolyZono.Float.Operations.Plus
import CORALean.ContSet.ConPolyZono.Float.Operations.Mtimes
import CORALean.ContSet.ConPolyZono.Float.Operations.Reduce

/-!
# What `ConPolyZono` computes

`plus` and `mtimes` pay their rounding into the error box and touch the
constraint system only by copying — `plus` places the two matrices
block-diagonally, `mtimes` leaves them alone. `dependent` copies everything and
rounds nothing at all.

`and` is the one that computes constraint data, and the one the representation
exists for. It is possible here only because the right-hand side of a constraint
is an interval: its agreement rows have to admit the difference of two nominal
points that each carry an error box, so they were never going to be an equality,
and the rounding of the centres rides along inside the same interval.

`compact` is the operation that pays into both places at once, and the only one
that does: merging generator columns rounds into the error box, merging
constraint columns into `b`, and dropping factors into neither.

`reduce` is the one operation computable here and not over ℝ, ranking generators
with a comparator that owes no laws. It pays nothing of its own: the box it adds
rounds outward, and the rounding it does is `compact`'s, which it runs first.
-/
