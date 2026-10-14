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
import CORALean.ContDynamics.LinearSys.Operations.Canonical

/-!
# A continuous-time linear system, checked against a box end to end

`ẋ = A x` with `A = [-1 1; 0 -2]`, from the box `[0, 2]²` as a zonotope, over
`[0, 1]` in windows of `Δt = 1/10` at Taylor order `4`. The flow contracts towards
the origin, so the reachable set never leaves the box it starts in, and the safe set is
that box with a margin of `1/2`, `[-1/2, 5/2]²`: tight enough that a check which
widened the enclosure past it would fail, checked on every window by `Contains`
through the zonotope's interval hull — the float box at `𝕋 := ℝ`, which is where the
checks live.

`reach` and `reachWrappingFree` both name `exp`, which is `pending #1`, so neither check
can be evaluated here; what is shown is that `holds_of_check_wrappingFree` applies as
stated at the system's own `reachWrappingFree`, kept but no longer the `Reach` instance,
and that the generic `Reach.holds_of_check` applies through that instance, now the
recursive `reach`, so a `true` from a float refinement would need nothing further to
answer for every trajectory. Inputs are `LinearSysInputCheck`'s business. The last example is a
failed run, at `Δt = 0`: `reach` returns `none`, so there is no set to enclose and
`check` is `false`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       24-September-2026
-- Last update:   14-October-2026
-- Reviewed:      ---

namespace CORALean.Real

open ContSet

-- Anonymous, since their content is that they elaborate.

/-- The safe box on the windows answers for every state the flow reaches by `1`. -/
example :
    (Specification.safeSet (⟨![-1 / 2, -1 / 2], ![5 / 2, 5 / 2]⟩ : Float.Interval (Vec ℝ 2))).check
      ((LinearSys.canonical !![-1, 1; 0, -2] : LinearSys ℝ 2).reachWrappingFree (S := 𝒵)
        ⟨(⟨2, ![1, 1], ![![1, 0], ![0, 1]]⟩ : Zonotope (Vec ℝ 2)), 0, 1⟩ ⟨1 / 10, 4⟩) →
    ((Specification.safeSet (⟨![-1 / 2, -1 / 2], ![5 / 2, 5 / 2]⟩ : Float.Interval (Vec ℝ 2))).Holds
      ((LinearSys.canonical !![-1, 1; 0, -2] : LinearSys ℝ 2).reachExact (1 - 0)
        (construct (⟨2, ![1, 1], ![![1, 0], ![0, 1]]⟩ : Zonotope (Vec ℝ 2))))) :=
  LinearSys.holds_of_check_wrappingFree (S := 𝒵) _ _ (by norm_num) _

/-- The same through `Reach.check`, CORA's `reach(sys, params, options)` and then `check`. -/
example :
    Reach.check (S := 𝒵) (LinearSys.canonical !![-1, 1; 0, -2] : LinearSys ℝ 2)
      ⟨(⟨2, ![1, 1], ![![1, 0], ![0, 1]]⟩ : Zonotope (Vec ℝ 2)), 0, 1⟩ ⟨1 / 10, 4⟩
      (Specification.safeSet (⟨![-1 / 2, -1 / 2], ![5 / 2, 5 / 2]⟩ : Float.Interval (Vec ℝ 2))) →
    ((Specification.safeSet (⟨![-1 / 2, -1 / 2], ![5 / 2, 5 / 2]⟩ : Float.Interval (Vec ℝ 2))).Holds
      (Reach.reachExact (S := 𝒵) (LinearSys.canonical !![-1, 1; 0, -2] : LinearSys ℝ 2)
        ⟨(⟨2, ![1, 1], ![![1, 0], ![0, 1]]⟩ : Zonotope (Vec ℝ 2)), 0, 1⟩)) :=
  Reach.holds_of_check (S := 𝒵) _ _ _ _

/-- At `Δt = 0` no window can be taken, and `reach` says so: no set, nothing to enclose. -/
example :
    Reach.reach (S := 𝒵) (LinearSys.canonical !![-1, 1; 0, -2] : LinearSys ℝ 2)
      ⟨(⟨2, ![1, 1], ![![1, 0], ![0, 1]]⟩ : Zonotope (Vec ℝ 2)), 0, 1⟩ ⟨0, 4⟩ = none :=
  if_neg fun h => lt_irrefl _ h.2

end CORALean.Real
