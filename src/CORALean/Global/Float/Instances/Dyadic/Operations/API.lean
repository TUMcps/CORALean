import CORALean.Global.Float.Instances.Dyadic.Operations.AddDown
import CORALean.Global.Float.Instances.Dyadic.Operations.AddUp
import CORALean.Global.Float.Instances.Dyadic.Operations.DivDown
import CORALean.Global.Float.Instances.Dyadic.Operations.DivUp
import CORALean.Global.Float.Instances.Dyadic.Operations.ExactAdd
import CORALean.Global.Float.Instances.Dyadic.Operations.ExactMul
import CORALean.Global.Float.Instances.Dyadic.Operations.Half
import CORALean.Global.Float.Instances.Dyadic.Operations.Le
import CORALean.Global.Float.Instances.Dyadic.Operations.Maximum
import CORALean.Global.Float.Instances.Dyadic.Operations.Minimum
import CORALean.Global.Float.Instances.Dyadic.Operations.MulDown
import CORALean.Global.Float.Instances.Dyadic.Operations.MulUp
import CORALean.Global.Float.Instances.Dyadic.Operations.Neg
import CORALean.Global.Float.Instances.Dyadic.Operations.QuotDown
import CORALean.Global.Float.Instances.Dyadic.Operations.QuotUp
import CORALean.Global.Float.Instances.Dyadic.Operations.RoundDown
import CORALean.Global.Float.Instances.Dyadic.Operations.RoundUp
import CORALean.Global.Float.Instances.Dyadic.Operations.Shift

/-!
# Dyadic numbers at a fixed precision: the operations, collected

Every rounded operation is exact-then-round: `exactAdd`/`exactMul` may overflow `p` bits — a
product needs `2p` — so they are separate from `roundUp`/`roundDown`, which return to the grid
by shifting the mantissa right by `shift` bits, taking the floor or the ceiling. Division is the
exception, and the only operation with no exact step: a quotient of dyadics is not dyadic, so
`quotUp`/`quotDown` round while dividing, and `divUp`/`divDown` round a second time past that.
`le`/`minimum`/`maximum` are exact, needing no rounding; `neg`/`half` touch the mantissa or the
exponent alone.
-/
