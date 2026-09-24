import CORALean.ContDynamics.LinParamSys.Definitions.ReachParams
import CORALean.ContSet.Interval.Real.Instances

/-!
# The exact set `Reach (LinParamSys ℐ)` is asked to enclose

Every image of a bare initial set under the homogeneous flow of every matrix
`sys.A` holds, at every time of `[0, p.r]` — `ConstTrajectory` at `U = 0`,
the reading `timeIntervalStep` is proved against.
-/

-- Authors:       Tobias Ladner
-- Written:       24-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix NormedSpace

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Every image of a bare initial set `X` under `exp (t • A)`, at every
`A ∈ construct sys.A` and every `t ∈ [0, p.r]`. -/
noncomputable def LinParamSys.reachUnionExact (sys : LinParamSys ℐ n)
    (p : LinParamSys.ReachParams) (X : Set (Vec ℝ n)) : Set (Vec ℝ n) :=
  {x | ∃ A ∈ ContSet.construct sys.A, ∃ t ∈ Set.Icc (0 : ℝ) p.r,
    ∃ x₀ ∈ X, x = exp (t • A) *ᵥ x₀}

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
