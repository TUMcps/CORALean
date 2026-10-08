import CORALean.Global.Float.Instances.Binary64.Operations.AddDown
import CORALean.Global.Float.Instances.Binary64.Operations.AddUp
import CORALean.Global.Float.Instances.Binary64.Operations.DivDown
import CORALean.Global.Float.Instances.Binary64.Operations.DivUp
import CORALean.Global.Float.Instances.Binary64.Operations.Half
import CORALean.Global.Float.Instances.Binary64.Operations.InRange
import CORALean.Global.Float.Instances.Binary64.Operations.Maximum
import CORALean.Global.Float.Instances.Binary64.Operations.Minimum
import CORALean.Global.Float.Instances.Binary64.Operations.MulDown
import CORALean.Global.Float.Instances.Binary64.Operations.MulUp
import CORALean.Global.Float.Instances.Binary64.Operations.NextUp
import CORALean.Global.Float.Instances.Binary64.Operations.StepUp

/-!
# Native binary64: the operations, collected

The machine rounds to nearest, which bounds nothing in a stated direction, so each upward
operation is the machine's followed by `stepUp`, one `nextUp` outward; each downward one is its
upward mirror between two negations, exact on a machine as it is on paper, which is what lets
the trusted property in `Definitions/TrustedHardware.lean` carry three inequalities, not six.
`half` is the one operation neither direction touches, assumed exact in `Definitions/Axioms.lean`.
Every rounded result is NaN outside binary64's normal range, the range the hardware is trusted
on; `neg` is not rounded, and `minimum`/`maximum` carry a NaN through where core's `min`/`max`
drop it.
-/
