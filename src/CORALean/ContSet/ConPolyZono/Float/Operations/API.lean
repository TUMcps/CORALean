import CORALean.ContSet.ConPolyZono.Float.Operations.And
import CORALean.ContSet.ConPolyZono.Float.Operations.Dependent
import CORALean.ContSet.ConPolyZono.Float.Operations.Plus
import CORALean.ContSet.ConPolyZono.Float.Operations.Mtimes

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
-/
