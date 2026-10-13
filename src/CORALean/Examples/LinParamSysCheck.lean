import CORALean.ContDynamics.LinParamSys.Instances
import CORALean.ContDynamics.Reach.Theorems.HoldsOfCheck
import CORALean.ContSet.Conversion.Float.ContSet_to_Interval
import CORALean.ContSet.Conversion.Real.ContSet_to_Interval
import CORALean.ContSet.SetUnion.Instances
import CORALean.ContSet.Zonotope.Real.Instances
import CORALean.ContSet.Zonotope.Real.Theorems.CentreMemConstruct
import CORALean.Global.Float.Instances.Real.Instances
import CORALean.Specification.Instances

/-!
# A system with an uncertain matrix, checked against a box end to end

`ẋ = A x (+ u)` with `A` anywhere in the interval matrix
`[-11/10, -9/10] [9/10, 11/10]; [0, 0] [-21/10, -19/10]`, fixed over each run
(`ConstTrajectory`), from the box `[0, 2]²` as a zonotope, over `[0, 1]` in
windows of `Δt = 1/10` at Taylor order `4` — `LinearSysCheck`'s system, its
matrix widened by a tenth. The safe box `[-10, 10]²` is checked on every window.

As there, `reach` names `exp` and cannot be evaluated here: what is shown is
that `Reach.holds_of_check` applies at `LinParamSys ℐ` and at
`LinParamSys.WithInput`, inputs in `[-1/10, 1/10]²`, so a `true` would answer
for every member of the matrix set and every run. The third example moves
that box off the origin, to `[9/10, 11/10] × [-1/10, 1/10]`, as
`LinParamSys.WithInputSplit`, which asks for no `0 ∈ U` at all.
-/

-- Authors:       Claude Opus 5.5
-- Written:       24-September-2026
-- Last update:   30-September-2026
-- Reviewed:      ---

namespace CORALean.Real

open ContSet

-- Anonymous, since their content is that they elaborate.

/-- The safe box on the windows answers for every member's flow by `1`. -/
example :
    Reach.check (S := 𝒵)
      (⟨⟨!![-11 / 10, 9 / 10; 0, -21 / 10], !![-9 / 10, 11 / 10; 0, -19 / 10]⟩⟩ :
        LinParamSys ℐ 2)
      ⟨(⟨2, ![1, 1], ![![1, 0], ![0, 1]]⟩ : Zonotope (Vec ℝ 2)), 0, 1⟩ ⟨1 / 10, 4⟩
      (Specification.safeSet (⟨![-10, -10], ![10, 10]⟩ : Float.Interval (Vec ℝ 2))) →
    ((Specification.safeSet (⟨![-10, -10], ![10, 10]⟩ : Float.Interval (Vec ℝ 2))).Holds
      (Reach.reachExact (S := 𝒵)
        (⟨⟨!![-11 / 10, 9 / 10; 0, -21 / 10], !![-9 / 10, 11 / 10; 0, -19 / 10]⟩⟩ :
          LinParamSys ℐ 2)
        ⟨(⟨2, ![1, 1], ![![1, 0], ![0, 1]]⟩ : Zonotope (Vec ℝ 2)), 0, 1⟩)) :=
  Reach.holds_of_check (S := 𝒵) _ _ _ _

/-- With inputs in `[-1/10, 1/10]²`: the same box answers for every run under them. -/
example :
    Reach.check (S := 𝒵)
      (⟨⟨⟨!![-11 / 10, 9 / 10; 0, -21 / 10], !![-9 / 10, 11 / 10; 0, -19 / 10]⟩⟩,
        ⟨2, 0, ![![1 / 10, 0], ![0, 1 / 10]]⟩, Zonotope.centre_mem_construct _⟩ :
          LinParamSys.WithInput 𝒵 2)
      ⟨(⟨2, ![1, 1], ![![1, 0], ![0, 1]]⟩ : Zonotope (Vec ℝ 2)), 0, 1⟩ ⟨1 / 10, 4⟩
      (Specification.safeSet (⟨![-10, -10], ![10, 10]⟩ : Float.Interval (Vec ℝ 2))) →
    ((Specification.safeSet (⟨![-10, -10], ![10, 10]⟩ : Float.Interval (Vec ℝ 2))).Holds
      (Reach.reachExact (S := 𝒵)
        (⟨⟨⟨!![-11 / 10, 9 / 10; 0, -21 / 10], !![-9 / 10, 11 / 10; 0, -19 / 10]⟩⟩,
          ⟨2, 0, ![![1 / 10, 0], ![0, 1 / 10]]⟩, Zonotope.centre_mem_construct _⟩ :
            LinParamSys.WithInput 𝒵 2)
        ⟨(⟨2, ![1, 1], ![![1, 0], ![0, 1]]⟩ : Zonotope (Vec ℝ 2)), 0, 1⟩)) :=
  Reach.holds_of_check (S := 𝒵) _ _ _ _

/-- With inputs in a box off the origin, split at its centre: the same answer. -/
example :
    Reach.check (S := 𝒵)
      (⟨⟨⟨!![-11 / 10, 9 / 10; 0, -21 / 10], !![-9 / 10, 11 / 10; 0, -19 / 10]⟩⟩,
        ⟨2, ![1, 0], ![![1 / 10, 0], ![0, 1 / 10]]⟩⟩ : LinParamSys.WithInputSplit 𝒵 2)
      ⟨(⟨2, ![1, 1], ![![1, 0], ![0, 1]]⟩ : Zonotope (Vec ℝ 2)), 0, 1⟩ ⟨1 / 10, 4⟩
      (Specification.safeSet (⟨![-10, -10], ![10, 10]⟩ : Float.Interval (Vec ℝ 2))) →
    ((Specification.safeSet (⟨![-10, -10], ![10, 10]⟩ : Float.Interval (Vec ℝ 2))).Holds
      (Reach.reachExact (S := 𝒵)
        (⟨⟨⟨!![-11 / 10, 9 / 10; 0, -21 / 10], !![-9 / 10, 11 / 10; 0, -19 / 10]⟩⟩,
          ⟨2, ![1, 0], ![![1 / 10, 0], ![0, 1 / 10]]⟩⟩ : LinParamSys.WithInputSplit 𝒵 2)
        ⟨(⟨2, ![1, 1], ![![1, 0], ![0, 1]]⟩ : Zonotope (Vec ℝ 2)), 0, 1⟩)) :=
  Reach.holds_of_check (S := 𝒵) _ _ _ _

end CORALean.Real
