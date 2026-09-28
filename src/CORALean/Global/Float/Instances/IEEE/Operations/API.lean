import CORALean.Global.Float.Instances.IEEE.Operations.AddDown
import CORALean.Global.Float.Instances.IEEE.Operations.AddUp
import CORALean.Global.Float.Instances.IEEE.Operations.DivDown
import CORALean.Global.Float.Instances.IEEE.Operations.DivUp
import CORALean.Global.Float.Instances.IEEE.Operations.GridShift
import CORALean.Global.Float.Instances.IEEE.Operations.Half
import CORALean.Global.Float.Instances.IEEE.Operations.Le
import CORALean.Global.Float.Instances.IEEE.Operations.Maximum
import CORALean.Global.Float.Instances.IEEE.Operations.Minimum
import CORALean.Global.Float.Instances.IEEE.Operations.MulDown
import CORALean.Global.Float.Instances.IEEE.Operations.MulUp
import CORALean.Global.Float.Instances.IEEE.Operations.Neg
import CORALean.Global.Float.Instances.IEEE.Operations.Overflows
import CORALean.Global.Float.Instances.IEEE.Operations.RoundDown
import CORALean.Global.Float.Instances.IEEE.Operations.RoundUp

/-!
# The formats of IEEE 754 and OCP MX: the operations, collected

Every rounded operation is `Dyadic`'s exact step, then `roundUp`/`roundDown` onto the grid of
the format: `gridShift` drops enough bits to leave `p` of them and to lift the exponent to the
smallest subnormal's. Division has no exact step and rounds twice, `Dyadic.divUp`/`divDown`
first. `neg`/`half`/`le`/`minimum`/`maximum` are exact, and `overflows` is the one operation no
class asks for: it says whether a value is past the format's largest finite number.
-/
