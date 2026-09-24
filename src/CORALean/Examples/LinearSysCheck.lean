import CORALean.ContDynamics.LinearSys.Instances
import CORALean.ContDynamics.LinearSys.Theorems.HoldsOfCheck
import CORALean.ContDynamics.Reach.Theorems.HoldsOfCheck
import CORALean.ContSet.Conversion.Float.ContSet_to_Interval
import CORALean.ContSet.Conversion.Real.ContSet_to_Interval
import CORALean.ContSet.SetUnion.Instances
import CORALean.ContSet.Zonotope.Real.Instances
import CORALean.Global.Float.Instances.Real.Instances
import CORALean.Specification.Instances

/-!
# A continuous-time linear system, checked against a box end to end

`ẋ = A x` with `A = [-1 1; 0 -2]`, from the box `[0, 2]²` as a zonotope, over
`[0, 1]` in windows of `Δt = 1/10` at Taylor order `4`. The safe set is the box
`[-10, 10]²`, checked on every window by `Contains` through the zonotope's
interval hull — the float box at `𝕋 := ℝ`, which is where the checks live.

`reach` names `exp`, which is `pending #1`, so the check cannot be evaluated
here; what is shown is that `holds_of_check` applies as stated, once at the
system's own `reach` and once through the `Reach` instance, so a `true` from a
float refinement would need nothing further to answer for every trajectory.
-/

-- Authors:       Tobias Ladner
-- Written:       24-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

open ContSet

-- Anonymous, since their content is that they elaborate.

/-- The safe box on the windows answers for every state the flow reaches by `1`. -/
example :
    ((Specification.safeSet (⟨![-10, -10], ![10, 10]⟩ : Float.Interval (Vec ℝ 2))).check
      ((⟨!![-1, 1; 0, -2]⟩ : LinearSys ℝ 2).reach (S := 𝒵) 1 (1 / 10) 4
        (⟨2, ![1, 1], ![![1, 0], ![0, 1]]⟩ : Zonotope (Vec ℝ 2))) = true) →
    ((Specification.safeSet (⟨![-10, -10], ![10, 10]⟩ : Float.Interval (Vec ℝ 2))).Holds
      ((⟨!![-1, 1; 0, -2]⟩ : LinearSys ℝ 2).reachExact 1
        (construct (⟨2, ![1, 1], ![![1, 0], ![0, 1]]⟩ : Zonotope (Vec ℝ 2))))) :=
  LinearSys.holds_of_check (S := 𝒵) _ (by norm_num) 4 _ _

/-- The same through `Reach.check`, the parameters bundled as `LinearSys.ReachParams`. -/
example :
    (Reach.check (S := 𝒵) (⟨!![-1, 1; 0, -2]⟩ : LinearSys ℝ 2)
      (⟨1, 1 / 10, 4, by norm_num⟩ : LinearSys.ReachParams)
      (⟨2, ![1, 1], ![![1, 0], ![0, 1]]⟩ : Zonotope (Vec ℝ 2))
      (Specification.safeSet (⟨![-10, -10], ![10, 10]⟩ : Float.Interval (Vec ℝ 2))) = true) →
    ((Specification.safeSet (⟨![-10, -10], ![10, 10]⟩ : Float.Interval (Vec ℝ 2))).Holds
      (Reach.reachExact (S := 𝒵) (⟨!![-1, 1; 0, -2]⟩ : LinearSys ℝ 2)
        (⟨1, 1 / 10, 4, by norm_num⟩ : LinearSys.ReachParams)
        (construct (⟨2, ![1, 1], ![![1, 0], ![0, 1]]⟩ : Zonotope (Vec ℝ 2))))) :=
  Reach.holds_of_check (S := 𝒵) _ _ _ _

end CORALean.Real
