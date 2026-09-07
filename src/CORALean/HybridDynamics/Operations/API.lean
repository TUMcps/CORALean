import CORALean.HybridDynamics.Operations.Jump
import CORALean.HybridDynamics.Operations.JumpAnd
import CORALean.HybridDynamics.Operations.JumpOfPoint
import CORALean.HybridDynamics.Operations.JumpAndOfPoint
import CORALean.HybridDynamics.Operations.TimeIntervalStep
import CORALean.HybridDynamics.Operations.TimeIntervalStepInv
import CORALean.HybridDynamics.Operations.TimeIntervalStepSplit

/-!
# What a hybrid automaton computes, collected

`Jump` propagates the reset over a set already cut to the guard; `JumpAnd`
cuts it there itself, at a representation with an `And` instance. The flow
enclosure is `LinearSys`'s, named again here only so that a statement about it
reads its representation off the location; `TimeIntervalStepInv` cuts it to
the invariant the same way, for a representation that has one, and
`TimeIntervalStepSplit` computes its input contribution without asking the
location's input set to hold the origin.

`JumpOfPoint`/`JumpAndOfPoint` are the same pair at `OfPoint`, the weaker class
the offset actually needs — what lets `ConPolyZono`, having no `OfInterval`
instance, jump at all (#38).
-/
