module

public import CORALean.Global.Float.Instances.IEEE.Operations.AddDown
public import CORALean.Global.Float.Instances.IEEE.Operations.AddUp
public import CORALean.Global.Float.Instances.IEEE.Operations.DivDown
public import CORALean.Global.Float.Instances.IEEE.Operations.DivUp
public import CORALean.Global.Float.Instances.IEEE.Operations.GridShift
public import CORALean.Global.Float.Instances.IEEE.Operations.Half
public import CORALean.Global.Float.Instances.IEEE.Operations.Le
public import CORALean.Global.Float.Instances.IEEE.Operations.Maximum
public import CORALean.Global.Float.Instances.IEEE.Operations.Minimum
public import CORALean.Global.Float.Instances.IEEE.Operations.MulDown
public import CORALean.Global.Float.Instances.IEEE.Operations.MulUp
public import CORALean.Global.Float.Instances.IEEE.Operations.Neg
public import CORALean.Global.Float.Instances.IEEE.Operations.Overflows
public import CORALean.Global.Float.Instances.IEEE.Operations.RoundDown
public import CORALean.Global.Float.Instances.IEEE.Operations.RoundUp

/-!
# The formats of IEEE 754 and OCP MX: the operations, collected

Every rounded operation is `Dyadic`'s exact step, then `roundUp`/`roundDown` onto the grid of
the format: `gridShift` drops enough bits to leave `p` of them and to lift the exponent to the
smallest subnormal's. Division has no exact step and rounds twice, `Dyadic.divUp`/`divDown`
first. `neg`/`half`/`le`/`minimum`/`maximum` are exact, and `overflows` is the one operation no
class asks for: it says whether a value is past the format's largest finite number.
-/
