import CORALean.ContSet.ConPolyZono.Float.Operations.Plus
import CORALean.ContSet.ConPolyZono.Float.Operations.Mtimes

/-!
# What `ConPolyZono` computes

`plus` and `mtimes`, both paying their rounding into the error box, and both
touching the constraint system only by copying — `plus` places the two matrices
block-diagonally, `mtimes` leaves them alone.

That is the whole list, and the reason is in the representation's docstring: an
equality constraint has no direction to round in, so an operation that computes
new constraint data cannot be refined at all without the exact layer admitting
either a slack factor or an interval right-hand side. `and` is that operation,
and it has no float counterpart here.
-/
