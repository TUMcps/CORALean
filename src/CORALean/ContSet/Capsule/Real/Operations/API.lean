import CORALean.ContSet.Capsule.Real.Operations.OfPoint
import CORALean.ContSet.Capsule.Real.Operations.SupportBound
import CORALean.ContSet.Capsule.Real.Operations.Empty
import CORALean.ContSet.Capsule.Real.Operations.Reindex
import CORALean.ContSet.Capsule.Real.Operations.Radius
import CORALean.ContSet.Capsule.Real.Operations.Project
import CORALean.ContSet.Capsule.Real.Operations.Plus
import CORALean.ContSet.Capsule.Real.Operations.PlusVec
import CORALean.ContSet.Capsule.Real.Operations.Mtimes
import CORALean.ContSet.Capsule.Real.Operations.MtimesCora

/-!
# What a capsule computes, collected

`ofPoint`: a capsule is closed under almost nothing, `Instances.lean` says
why, but a degenerate one — no direction, no radius — still names the point
it collapses to. `supportBound` answers any direction in closed form, the
segment and the ball each contributing their own term.
-/
