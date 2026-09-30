import CORALean.ContDynamics.NonlinParamSys.Instances
import CORALean.ContDynamics.Reach.Theorems.HoldsOfCheck
import CORALean.ContSet.Conversion.Float.ContSet_to_Interval
import CORALean.ContSet.Conversion.Real.ContSet_to_Interval
import CORALean.ContSet.Conversion.Real.Interval_to_ContSet
import CORALean.ContSet.SetUnion.Instances
import CORALean.ContSet.Zonotope.Real.Instances
import CORALean.Global.Float.Instances.Real.Instances
import CORALean.Specification.Instances

/-!
# The parametric nonlinear class, checked through `Reach`

`Reach.holds_of_check` at `NonlinParamSys.WithSteps`, propagating zonotopes, a
two-dimensional state with one input and one uncertain parameter, and the float
box at `𝕋 := ℝ` as the region the augmented run is tested against, in dimension
`2 + 1`, and as the safe set, in dimension `2`. What is shown is that instance
search finds the instance with the parameter dimension fixed, and that a `true`
then answers for every constant-parameter trajectory, no confinement assumed.
-/

-- Authors:       Tobias Ladner
-- Written:       24-September-2026
-- Last update:   30-September-2026
-- Last revision: ---

namespace CORALean.Real

open ContSet

-- Anonymous, since its content is that it elaborates.

/-- A parametric system, its augmented run's region tests and `Reach.check`. -/
example (sys : NonlinParamSys.WithSteps 𝒵 (fun n => Float.Interval (Vec ℝ n)) 1 1 2)
    (params : Reach.Params (Zonotope (Vec ℝ 2)) ℝ) (options : LinearSys.ReachOptions ℝ)
    (spec : Specification (Float.Interval (Vec ℝ 2))) :
    Reach.check (S := 𝒵) sys params options spec →
    (spec.Holds (Reach.reachExact (S := 𝒵) sys params)) :=
  Reach.holds_of_check _ _ _ _

end CORALean.Real
