import CORALean.ContDynamics.LinearSys.Instances
import CORALean.ContDynamics.LinearSys.Theorems.HoldsOfCheckWrappingFree
import CORALean.ContDynamics.Reach.Theorems.HoldsOfCheck
import CORALean.ContSet.Conversion.Float.ContSet_to_Interval
import CORALean.ContSet.Conversion.Real.ContSet_to_Interval
import CORALean.ContSet.SetUnion.Instances
import CORALean.ContSet.Zonotope.Real.Instances
import CORALean.ContSet.Zonotope.Real.Theorems.CentreMemConstruct
import CORALean.Global.Float.Instances.Real.Instances
import CORALean.Specification.Instances

/-!
# A continuous-time linear system, checked against a box end to end

`ẋ = A x` with `A = [-1 1; 0 -2]`, from the box `[0, 2]²` as a zonotope, over
`[0, 1]` in windows of `Δt = 1/10` at Taylor order `4`. The safe set is the box
`[-10, 10]²`, checked on every window by `Contains` through the zonotope's
interval hull — the float box at `𝕋 := ℝ`, which is where the checks live.

`reach` and `reachWrappingFree` both name `exp`, which is `pending #1`, so neither check
can be evaluated here; what is shown is that `holds_of_check_wrappingFree` applies as
stated at the system's own `reachWrappingFree`, kept but no longer the `Reach` instance,
and that the generic `Reach.holds_of_check` applies through that instance, now the
recursive `reach`, so a `true` from a float refinement would need nothing further to
answer for every trajectory.
The third example adds the input box `[-1/10, 1/10]²` as `LinearSys.WithInput`,
its `0 ∈ U` the zonotope's centre, and answers for every run under it; the
fourth moves that box off the origin, to `[1/10, 3/10] × [-1/10, 1/10]`, as
`LinearSys.WithInputSplit`, which asks for no `0 ∈ U` at all.
-/

-- Authors:       Tobias Ladner
-- Written:       24-September-2026
-- Last update:   30-September-2026
-- Last revision: ---

namespace CORALean.Real

open ContSet

-- Anonymous, since their content is that they elaborate.

/-- The safe box on the windows answers for every state the flow reaches by `1`. -/
example :
    (Specification.safeSet (⟨![-10, -10], ![10, 10]⟩ : Float.Interval (Vec ℝ 2))).check
      ((⟨!![-1, 1; 0, -2]⟩ : LinearSys ℝ 2).reachWrappingFree (S := 𝒵)
        ⟨(⟨2, ![1, 1], ![![1, 0], ![0, 1]]⟩ : Zonotope (Vec ℝ 2)), 0, 1⟩ ⟨1 / 10, 4⟩) →
    ((Specification.safeSet (⟨![-10, -10], ![10, 10]⟩ : Float.Interval (Vec ℝ 2))).Holds
      ((⟨!![-1, 1; 0, -2]⟩ : LinearSys ℝ 2).reachExact (1 - 0)
        (construct (⟨2, ![1, 1], ![![1, 0], ![0, 1]]⟩ : Zonotope (Vec ℝ 2))))) :=
  LinearSys.holds_of_check_wrappingFree (S := 𝒵) _ _ (by norm_num) _

/-- The same through `Reach.check`, the parameters bundled as `LinearSys.ReachParams`. -/
example :
    Reach.check (S := 𝒵) (⟨!![-1, 1; 0, -2]⟩ : LinearSys ℝ 2)
      (⟨1, 1 / 10, 4, by norm_num⟩ : LinearSys.ReachParams)
      (⟨2, ![1, 1], ![![1, 0], ![0, 1]]⟩ : Zonotope (Vec ℝ 2))
      (Specification.safeSet (⟨![-10, -10], ![10, 10]⟩ : Float.Interval (Vec ℝ 2))) →
    ((Specification.safeSet (⟨![-10, -10], ![10, 10]⟩ : Float.Interval (Vec ℝ 2))).Holds
      (Reach.reachExact (S := 𝒵) (⟨!![-1, 1; 0, -2]⟩ : LinearSys ℝ 2)
        (⟨1, 1 / 10, 4, by norm_num⟩ : LinearSys.ReachParams)
        (construct (⟨2, ![1, 1], ![![1, 0], ![0, 1]]⟩ : Zonotope (Vec ℝ 2))))) :=
  Reach.holds_of_check (S := 𝒵) _ _ _ _

/-- With inputs in `[-1/10, 1/10]²`: the same box answers for every run under them. -/
example :
    Reach.check (S := 𝒵)
      (⟨⟨!![-1, 1; 0, -2]⟩, ⟨2, 0, ![![1 / 10, 0], ![0, 1 / 10]]⟩,
        Zonotope.centre_mem_construct _⟩ : LinearSys.WithInput ℝ 𝒵 2)
      (⟨1, 1 / 10, 4, by norm_num⟩ : LinearSys.ReachParams)
      (⟨2, ![1, 1], ![![1, 0], ![0, 1]]⟩ : Zonotope (Vec ℝ 2))
      (Specification.safeSet (⟨![-10, -10], ![10, 10]⟩ : Float.Interval (Vec ℝ 2))) →
    ((Specification.safeSet (⟨![-10, -10], ![10, 10]⟩ : Float.Interval (Vec ℝ 2))).Holds
      (Reach.reachExact (S := 𝒵)
        (⟨⟨!![-1, 1; 0, -2]⟩, ⟨2, 0, ![![1 / 10, 0], ![0, 1 / 10]]⟩,
          Zonotope.centre_mem_construct _⟩ : LinearSys.WithInput ℝ 𝒵 2)
        (⟨1, 1 / 10, 4, by norm_num⟩ : LinearSys.ReachParams)
        (construct (⟨2, ![1, 1], ![![1, 0], ![0, 1]]⟩ : Zonotope (Vec ℝ 2))))) :=
  Reach.holds_of_check (S := 𝒵) _ _ _ _

/-- With inputs in a box off the origin, split at its centre: the same answer. -/
example :
    Reach.check (S := 𝒵)
      (⟨⟨!![-1, 1; 0, -2]⟩, ⟨2, ![1 / 5, 0], ![![1 / 10, 0], ![0, 1 / 10]]⟩⟩ :
        LinearSys.WithInputSplit ℝ 𝒵 2)
      (⟨1, 1 / 10, 4, by norm_num⟩ : LinearSys.ReachParams)
      (⟨2, ![1, 1], ![![1, 0], ![0, 1]]⟩ : Zonotope (Vec ℝ 2))
      (Specification.safeSet (⟨![-10, -10], ![10, 10]⟩ : Float.Interval (Vec ℝ 2))) →
    ((Specification.safeSet (⟨![-10, -10], ![10, 10]⟩ : Float.Interval (Vec ℝ 2))).Holds
      (Reach.reachExact (S := 𝒵)
        (⟨⟨!![-1, 1; 0, -2]⟩, ⟨2, ![1 / 5, 0], ![![1 / 10, 0], ![0, 1 / 10]]⟩⟩ :
          LinearSys.WithInputSplit ℝ 𝒵 2)
        (⟨1, 1 / 10, 4, by norm_num⟩ : LinearSys.ReachParams)
        (construct (⟨2, ![1, 1], ![![1, 0], ![0, 1]]⟩ : Zonotope (Vec ℝ 2))))) :=
  Reach.holds_of_check (S := 𝒵) _ _ _ _

end CORALean.Real
