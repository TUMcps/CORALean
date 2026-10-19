module

public import CORALean.Global.Float.Instances.Binary64.Operations.Basic
public import CORALean.Global.Float.Instances.Binary64.Operations.AddUp
public import CORALean.Global.Float.Instances.Binary64.Operations.DivDown
public import CORALean.Global.Float.Instances.Binary64.Operations.DivUp
public import CORALean.Global.Float.Instances.Binary64.Operations.Half
public import CORALean.Global.Float.Instances.Binary64.Operations.MulUp
public import CORALean.Global.Float.Instances.Binary64.Operations.NextUp
public import CORALean.Global.Float.Instances.Binary64.Operations.StepUp

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
