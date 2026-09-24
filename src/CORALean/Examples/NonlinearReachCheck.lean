import CORALean.ContDynamics.NonlinearSys.Instances
import CORALean.ContDynamics.NonlinearSysDT.Instances
import CORALean.ContDynamics.Reach.Theorems.HoldsOfCheck
import CORALean.ContSet.Conversion.Float.ContSet_to_Interval
import CORALean.ContSet.Conversion.Real.ContSet_to_Interval
import CORALean.ContSet.Conversion.Real.Interval_to_ContSet
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

-- Authors:       Tobias Ladner
-- Written:       24-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

open ContSet

-- Anonymous, since their content is that they elaborate.

/-- A discrete nonlinear system, its region tests and the check run by `Reach.check`. -/
example (sys : NonlinearSysDT.WithSteps (fun n => Interval (Vec ℝ n))
      (fun n => Float.Interval (Vec ℝ n)) 1 2)
    (p : NonlinearSysDT.ReachParams) (X₀ : Interval (Vec ℝ 2))
    (spec : Specification (Float.Interval (Vec ℝ 2))) :
    (Reach.check (S := fun n => Interval (Vec ℝ n)) sys p X₀ spec = true) →
    (spec.Holds (Reach.reachExact (S := fun n => Interval (Vec ℝ n)) sys p (construct X₀))) :=
  Reach.holds_of_check _ _ _ _

/-- The continuous case, the ball test `2MΔt` about each step's start run by `reach`. -/
example (sys : NonlinearSys.WithSteps 𝒵 (fun n => Float.Interval (Vec ℝ n)) 1 2)
    (p : NonlinearSys.ReachParams) (X₀ : Zonotope (Vec ℝ 2))
    (spec : Specification (Float.Interval (Vec ℝ 2))) :
    (Reach.check (S := 𝒵) sys p X₀ spec = true) →
    (spec.Holds (Reach.reachExact (S := 𝒵) sys p (construct X₀))) :=
  Reach.holds_of_check _ _ _ _

end CORALean.Real
