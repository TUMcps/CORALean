import CORALean.ContSet.HPolytope.Float.Operations.And
import CORALean.ContSet.HPolytope.Float.Operations.Certified
import CORALean.ContSet.HPolytope.Float.Operations.DualBound
import CORALean.ContSet.HPolytope.Float.Operations.OfBounds
import CORALean.ContSet.HPolytope.Float.Operations.OfMat
import CORALean.ContSet.HPolytope.Float.Operations.Pad
import CORALean.ContSet.HPolytope.Float.Operations.Translate

/-!
# What the float `HPolytope` computes

Three groups.

Exactly and without arithmetic: `and` concatenates constraint lists, `padLeft`
and `padRight` widen the coefficient space with zeros, and the two constructors
copy matrices. None of them rounds, because none of them computes.

Rounding, and where it goes: `translate` moves each bound by what its row reads
off the shift, an inequality absorbing that upward and an equality outward at
both ends of its interval. This is what the interval right-hand side is for, and
the only operation here that needs it.

Enclosing on chosen directions: `plusOf`, `linCombOf`, `mtimesOf` and
`intervalOf`, whose rows nobody can predict from the inputs' — `ofBounds` is
their shared shape and `DualBound` is where a halfspace description certifies a
direction for itself.
-/
