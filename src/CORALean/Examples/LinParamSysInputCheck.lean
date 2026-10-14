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
# An uncertain matrix under an input, checked against a box

`LinParamSysCheck`'s system, `ẋ = A x + u` with `A` anywhere in the interval matrix
`[-11/10, -9/10] [9/10, 11/10]; [0, 0] [-21/10, -19/10]`, from the box `[0, 2]²`, now
driven by an input set, against the safe box `[-1/2, 5/2]²`. In the first example the
input box is `[-1/10, 1/10]²` as `LinParamSys.WithInput`, and a `true` would answer for
every member of the matrix set and every run under it.

In the second the input box moves off the origin, to `[9/10, 11/10] × [-1/10, 1/10]`, as
`LinParamSys.WithInputSplit`, which asks for no `0 ∈ U` at all. As there, `reach` names
`exp` and cannot be evaluated here; what is shown is that `Reach.holds_of_check` applies at
both.
-/

-- Authors:       Claude Opus 5.5, Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


namespace CORALean.Real

open ContSet

-- Anonymous, since their content is that they elaborate.

/-- With inputs in `[-1/10, 1/10]²`: the same box answers for every run under them. -/
example :
    Reach.check (S := 𝒵)
      (⟨LinParamSys.canonical
          ⟨!![-11 / 10, 9 / 10; 0, -21 / 10], !![-9 / 10, 11 / 10; 0, -19 / 10]⟩,
        ⟨2, 0, ![![1 / 10, 0], ![0, 1 / 10]]⟩, Zonotope.centre_mem_construct _⟩ :
          LinParamSys.WithInput 𝒵 2)
      ⟨(⟨2, ![1, 1], ![![1, 0], ![0, 1]]⟩ : Zonotope (Vec ℝ 2)), 0, 1⟩ ⟨1 / 10, 4⟩
      (Specification.safeSet (⟨![-1 / 2, -1 / 2], ![5 / 2, 5 / 2]⟩ : Float.Interval (Vec ℝ 2))) →
    ((Specification.safeSet (⟨![-1 / 2, -1 / 2], ![5 / 2, 5 / 2]⟩ : Float.Interval (Vec ℝ 2))).Holds
      (Reach.reachExact (S := 𝒵)
        (⟨LinParamSys.canonical
            ⟨!![-11 / 10, 9 / 10; 0, -21 / 10], !![-9 / 10, 11 / 10; 0, -19 / 10]⟩,
          ⟨2, 0, ![![1 / 10, 0], ![0, 1 / 10]]⟩, Zonotope.centre_mem_construct _⟩ :
            LinParamSys.WithInput 𝒵 2)
        ⟨(⟨2, ![1, 1], ![![1, 0], ![0, 1]]⟩ : Zonotope (Vec ℝ 2)), 0, 1⟩)) :=
  Reach.holds_of_check (S := 𝒵) _ _ _ _

/-- With inputs in a box off the origin, split at its centre: the same answer. -/
example :
    Reach.check (S := 𝒵)
      (⟨LinParamSys.canonical
          ⟨!![-11 / 10, 9 / 10; 0, -21 / 10], !![-9 / 10, 11 / 10; 0, -19 / 10]⟩,
        ⟨2, ![1, 0], ![![1 / 10, 0], ![0, 1 / 10]]⟩⟩ : LinParamSys.WithInputSplit 𝒵 2)
      ⟨(⟨2, ![1, 1], ![![1, 0], ![0, 1]]⟩ : Zonotope (Vec ℝ 2)), 0, 1⟩ ⟨1 / 10, 4⟩
      (Specification.safeSet (⟨![-1 / 2, -1 / 2], ![5 / 2, 5 / 2]⟩ : Float.Interval (Vec ℝ 2))) →
    ((Specification.safeSet (⟨![-1 / 2, -1 / 2], ![5 / 2, 5 / 2]⟩ : Float.Interval (Vec ℝ 2))).Holds
      (Reach.reachExact (S := 𝒵)
        (⟨LinParamSys.canonical
            ⟨!![-11 / 10, 9 / 10; 0, -21 / 10], !![-9 / 10, 11 / 10; 0, -19 / 10]⟩,
          ⟨2, ![1, 0], ![![1 / 10, 0], ![0, 1 / 10]]⟩⟩ : LinParamSys.WithInputSplit 𝒵 2)
        ⟨(⟨2, ![1, 1], ![![1, 0], ![0, 1]]⟩ : Zonotope (Vec ℝ 2)), 0, 1⟩)) :=
  Reach.holds_of_check (S := 𝒵) _ _ _ _

end CORALean.Real
