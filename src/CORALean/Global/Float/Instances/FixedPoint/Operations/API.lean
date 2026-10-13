module

public import CORALean.Global.Float.Instances.FixedPoint.Operations.AddDown
public import CORALean.Global.Float.Instances.FixedPoint.Operations.AddUp
public import CORALean.Global.Float.Instances.FixedPoint.Operations.DivDown
public import CORALean.Global.Float.Instances.FixedPoint.Operations.DivUp
public import CORALean.Global.Float.Instances.FixedPoint.Operations.ExactAdd
public import CORALean.Global.Float.Instances.FixedPoint.Operations.ExactMul
public import CORALean.Global.Float.Instances.FixedPoint.Operations.Half
public import CORALean.Global.Float.Instances.FixedPoint.Operations.Le
public import CORALean.Global.Float.Instances.FixedPoint.Operations.Maximum
public import CORALean.Global.Float.Instances.FixedPoint.Operations.Minimum
public import CORALean.Global.Float.Instances.FixedPoint.Operations.MulDown
public import CORALean.Global.Float.Instances.FixedPoint.Operations.MulUp
public import CORALean.Global.Float.Instances.FixedPoint.Operations.Neg
public import CORALean.Global.Float.Instances.FixedPoint.Operations.RoundDown
public import CORALean.Global.Float.Instances.FixedPoint.Operations.RoundUp

/-!
# Fixed-point numbers at a target precision: the operations, collected

Every rounded operation but division is exact-then-round: `exactAdd`/`exactMul`
compute the sum or product exactly, at a digit count that may exceed `f`, and
`roundUp`/`roundDown` return to `f` digits by padding with zeros (below `f`) or
taking the floor or ceiling of the excess (past it). Division has no exact step
-- a quotient of fixed-point values is not one -- so `divUp`/`divDown` floor or
ceil the exact rational straight to `f` digits. `le`/`minimum`/`maximum` are
exact, needing no rounding; `neg` touches the mantissa alone and `half` adds one
digit.
-/
