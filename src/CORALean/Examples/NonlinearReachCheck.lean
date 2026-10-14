import CORALean.ContDynamics.NonlinearSys.Instances
import CORALean.ContDynamics.NonlinearSysDT.Instances
import CORALean.ContDynamics.Reach.Theorems.HoldsOfCheck
import CORALean.ContSet.Conversion.Float.Instances
import CORALean.ContSet.Conversion.Real.Instances
import CORALean.ContSet.SetUnion.Instances
import CORALean.ContSet.Zonotope.Real.Instances
import CORALean.Global.Float.Instances.Real.Instances
import CORALean.Specification.Instances

/-!
# The nonlinear classes, checked through `Reach`

`Reach.holds_of_check` at `NonlinearSysDT.WithSteps`, propagating boxes, and at
`NonlinearSys.WithSteps`, propagating zonotopes, each with the float box at
`𝕋 := ℝ` as the region its run-time test is asked against and as the safe set.
What is shown is that instance search finds both instances, `S`, the region
family and the input dimension all fixed, and that a `true` then needs nothing
further — no confinement of any run — to answer for every trajectory.
-/

-- Authors:       Claude Opus 5.5
-- Written:       24-September-2026
-- Last update:   30-September-2026
-- Reviewed:      ---

namespace CORALean.Real

open ContSet
open scoped CORALean.Float

-- Anonymous, since their content is that they elaborate.

/-- A discrete nonlinear system, its region tests and the check run by `Reach.check`. -/
example (sys : NonlinearSysDT.WithSteps ℐ𝒱
      ℐ𝒱[ℝ] ℝ 1 2)
    (params : Reach.Params (Interval (Vec ℝ 2)) ℕ) (options : NonlinearSysDT.ReachOptions)
    (spec : Specification (Float.Interval (Vec ℝ 2))) :
    Reach.check (S := ℐ𝒱) sys params options spec →
    (spec.Holds (Reach.reachExact (S := ℐ𝒱) sys params)) :=
  Reach.holds_of_check _ _ _ _

/-- The continuous case, the ball test `2MΔt` about each step's start run by `reach`. -/
example (sys : NonlinearSys.WithSteps 𝒵 ℐ𝒱[ℝ] 1 2)
    (params : Reach.Params (Zonotope (Vec ℝ 2)) ℝ) (options : LinearSys.ReachOptions ℝ)
    (spec : Specification (Float.Interval (Vec ℝ 2))) :
    Reach.check (S := 𝒵) sys params options spec →
    (spec.Holds (Reach.reachExact (S := 𝒵) sys params)) :=
  Reach.holds_of_check _ _ _ _

end CORALean.Real
