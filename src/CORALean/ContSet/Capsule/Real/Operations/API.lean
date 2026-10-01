import CORALean.ContSet.Capsule.Real.Operations.OfPoint
import CORALean.ContSet.Capsule.Real.Operations.SupportBound
import CORALean.ContSet.Capsule.Real.Operations.Empty

/-!
# What a capsule computes, collected

`ofPoint`: a capsule is closed under almost nothing, `Instances.lean` says
why, but a degenerate one — no direction, no radius — still names the point
it collapses to. `supportBound` answers any direction in closed form, the
segment and the ball each contributing their own term.
-/
