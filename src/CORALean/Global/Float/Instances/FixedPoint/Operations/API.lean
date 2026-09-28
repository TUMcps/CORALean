import CORALean.Global.Float.Instances.FixedPoint.Operations.AddDown
import CORALean.Global.Float.Instances.FixedPoint.Operations.AddUp
import CORALean.Global.Float.Instances.FixedPoint.Operations.DivDown
import CORALean.Global.Float.Instances.FixedPoint.Operations.DivUp
import CORALean.Global.Float.Instances.FixedPoint.Operations.ExactAdd
import CORALean.Global.Float.Instances.FixedPoint.Operations.ExactMul
import CORALean.Global.Float.Instances.FixedPoint.Operations.Half
import CORALean.Global.Float.Instances.FixedPoint.Operations.Le
import CORALean.Global.Float.Instances.FixedPoint.Operations.Maximum
import CORALean.Global.Float.Instances.FixedPoint.Operations.Minimum
import CORALean.Global.Float.Instances.FixedPoint.Operations.MulDown
import CORALean.Global.Float.Instances.FixedPoint.Operations.MulUp
import CORALean.Global.Float.Instances.FixedPoint.Operations.Neg
import CORALean.Global.Float.Instances.FixedPoint.Operations.RoundDown
import CORALean.Global.Float.Instances.FixedPoint.Operations.RoundUp

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
