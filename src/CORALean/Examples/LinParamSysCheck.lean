import CORALean.ContDynamics.LinParamSys.Instances
import CORALean.ContDynamics.Reach.Theorems.HoldsOfCheck
import CORALean.ContSet.Conversion.Float.Instances
import CORALean.ContSet.Conversion.Real.Instances
import CORALean.ContSet.SetUnion.Instances
import CORALean.ContSet.Zonotope.Real.Instances
import CORALean.ContSet.Zonotope.Real.Theorems.CentreMemConstruct
import CORALean.Global.Float.Instances.Real.Instances
import CORALean.Specification.Instances
import CORALean.ContDynamics.LinParamSys.Operations.Canonical

/-!
# A system with an uncertain matrix, checked against a box end to end

`ẋ = A x` with `A` anywhere in the interval matrix
`[-11/10, -9/10] [9/10, 11/10]; [0, 0] [-21/10, -19/10]`, fixed over each run
(`ConstTrajectory`), from the box `[0, 2]²` as a zonotope, over `[0, 1]` in
windows of `Δt = 1/10` at Taylor order `4` — `LinearSysCheck`'s system, its
matrix widened by a tenth. Every member still contracts, so the safe box is
`LinearSysCheck`'s, `[-1/2, 5/2]²`, checked on every window.

As there, `reach` names `exp` and cannot be evaluated here: what is shown is
that `Reach.holds_of_check` applies at `LinParamSys ℐ`, so a `true` would
answer for every member of the matrix set. Inputs are `LinParamSysInputCheck`'s
business.
-/

-- Authors:       Claude Opus 5.5
-- Written:       24-September-2026
-- Last update:   14-October-2026
-- Reviewed:      ---

namespace CORALean.Real

open ContSet

-- Anonymous, since their content is that they elaborate.

/-- The safe box on the windows answers for every member's flow by `1`. -/
example :
    Reach.check (S := 𝒵)
      (LinParamSys.canonical
          ⟨!![-11 / 10, 9 / 10; 0, -21 / 10], !![-9 / 10, 11 / 10; 0, -19 / 10]⟩ :
        LinParamSys ℐ 2)
      ⟨(⟨2, ![1, 1], ![![1, 0], ![0, 1]]⟩ : Zonotope (Vec ℝ 2)), 0, 1⟩ ⟨1 / 10, 4⟩
      (Specification.safeSet (⟨![-1 / 2, -1 / 2], ![5 / 2, 5 / 2]⟩ : Float.Interval (Vec ℝ 2))) →
    ((Specification.safeSet (⟨![-1 / 2, -1 / 2], ![5 / 2, 5 / 2]⟩ : Float.Interval (Vec ℝ 2))).Holds
      (Reach.reachExact (S := 𝒵)
        (LinParamSys.canonical
            ⟨!![-11 / 10, 9 / 10; 0, -21 / 10], !![-9 / 10, 11 / 10; 0, -19 / 10]⟩ :
          LinParamSys ℐ 2)
        ⟨(⟨2, ![1, 1], ![![1, 0], ![0, 1]]⟩ : Zonotope (Vec ℝ 2)), 0, 1⟩)) :=
  Reach.holds_of_check (S := 𝒵) _ _ _ _

end CORALean.Real
