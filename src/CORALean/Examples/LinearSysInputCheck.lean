import CORALean.ContDynamics.LinearSys.Instances
import CORALean.ContDynamics.LinearSys.Theorems.HoldsOfCheckWrappingFree
import CORALean.ContDynamics.Reach.Theorems.HoldsOfCheck
import CORALean.ContSet.Conversion.Float.Instances
import CORALean.ContSet.Conversion.Real.Instances
import CORALean.ContSet.SetUnion.Instances
import CORALean.ContSet.Zonotope.Real.Instances
import CORALean.ContSet.Zonotope.Real.Theorems.CentreMemConstruct
import CORALean.Global.Float.Instances.Real.Instances
import CORALean.Specification.Instances
import CORALean.ContDynamics.LinearSys.Operations.Canonical

/-!
# A linear system under an input, checked against a box

`LinearSysCheck`'s system, `ẋ = A x + u` with `A = [-1 1; 0 -2]`, from the box
`[0, 2]²`, now driven by an input set. In the first example the input box is
`[-1/10, 1/10]²` as `LinearSys.WithInput`, its `0 ∈ U` the zonotope's centre, and
the answer holds for every run under it. The input is small against the safe box
`[-1/2, 5/2]²`, whose margin of `1/2` is what the contraction leaves it.

In the second the input box moves off the origin, to `[1/10, 3/10] × [-1/10, 1/10]`, as
`LinearSys.WithInputSplit`, which asks for no `0 ∈ U` at all: it is split at its centre
into a constant and a zero-centred part. As there, `reach` names `exp` and cannot be
evaluated here; what is shown is that `Reach.holds_of_check` applies at both.
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
      (⟨LinearSys.canonical !![-1, 1; 0, -2], ⟨2, 0, ![![1 / 10, 0], ![0, 1 / 10]]⟩,
        Zonotope.centre_mem_construct _⟩ : LinearSys.WithInput ℝ 𝒵 2)
      ⟨(⟨2, ![1, 1], ![![1, 0], ![0, 1]]⟩ : Zonotope (Vec ℝ 2)), 0, 1⟩ ⟨1 / 10, 4⟩
      (Specification.safeSet (⟨![-1 / 2, -1 / 2], ![5 / 2, 5 / 2]⟩ : Float.Interval (Vec ℝ 2))) →
    ((Specification.safeSet (⟨![-1 / 2, -1 / 2], ![5 / 2, 5 / 2]⟩ : Float.Interval (Vec ℝ 2))).Holds
      (Reach.reachExact (S := 𝒵)
        (⟨LinearSys.canonical !![-1, 1; 0, -2], ⟨2, 0, ![![1 / 10, 0], ![0, 1 / 10]]⟩,
          Zonotope.centre_mem_construct _⟩ : LinearSys.WithInput ℝ 𝒵 2)
        ⟨(⟨2, ![1, 1], ![![1, 0], ![0, 1]]⟩ : Zonotope (Vec ℝ 2)), 0, 1⟩)) :=
  Reach.holds_of_check (S := 𝒵) _ _ _ _

/-- With inputs in a box off the origin, split at its centre: the same answer. -/
example :
    Reach.check (S := 𝒵)
      (⟨LinearSys.canonical !![-1, 1; 0, -2], ⟨2, ![1 / 5, 0], ![![1 / 10, 0], ![0, 1 / 10]]⟩⟩ :
        LinearSys.WithInputSplit ℝ 𝒵 2)
      ⟨(⟨2, ![1, 1], ![![1, 0], ![0, 1]]⟩ : Zonotope (Vec ℝ 2)), 0, 1⟩ ⟨1 / 10, 4⟩
      (Specification.safeSet (⟨![-1 / 2, -1 / 2], ![5 / 2, 5 / 2]⟩ : Float.Interval (Vec ℝ 2))) →
    ((Specification.safeSet (⟨![-1 / 2, -1 / 2], ![5 / 2, 5 / 2]⟩ : Float.Interval (Vec ℝ 2))).Holds
      (Reach.reachExact (S := 𝒵)
        (⟨LinearSys.canonical !![-1, 1; 0, -2], ⟨2, ![1 / 5, 0], ![![1 / 10, 0], ![0, 1 / 10]]⟩⟩ :
          LinearSys.WithInputSplit ℝ 𝒵 2)
        ⟨(⟨2, ![1, 1], ![![1, 0], ![0, 1]]⟩ : Zonotope (Vec ℝ 2)), 0, 1⟩)) :=
  Reach.holds_of_check (S := 𝒵) _ _ _ _

end CORALean.Real
