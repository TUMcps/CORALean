import CORALean.Global.Float.Instances.Binary64.Operations.AddDown
import CORALean.Global.Float.Instances.Binary64.Operations.AddUp
import CORALean.Global.Float.Instances.Binary64.Operations.DivDown
import CORALean.Global.Float.Instances.Binary64.Operations.DivUp
import CORALean.Global.Float.Instances.Binary64.Operations.Half
import CORALean.Global.Float.Instances.Binary64.Operations.MulDown
import CORALean.Global.Float.Instances.Binary64.Operations.MulUp
import CORALean.Global.Float.Instances.Binary64.Operations.NextUp

/-!
# Native binary64: the operations, collected

The machine rounds to nearest, which bounds nothing in a stated direction, so each upward
operation is the machine's followed by `nextUp`, one step outward; each downward one is its
upward mirror between two negations, exact on a machine as it is on paper, which is what lets
the trusted property in `Definitions/TrustedHardware.lean` carry three inequalities, not six.
`half` is the one operation neither direction touches, assumed exact in `Definitions/Axioms.lean`.
-/
