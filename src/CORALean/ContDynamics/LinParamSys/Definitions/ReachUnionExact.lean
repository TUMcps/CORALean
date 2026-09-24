import CORALean.ContDynamics.LinParamSys.LinParamSys
import CORALean.ContDynamics.LinearSys.Definitions.ReachParams
import CORALean.ContSet.Interval.Real.Instances

/-!
# The exact set `Reach (LinParamSys ℐ)` is asked to enclose

Every image of a bare initial set under the homogeneous flow of every matrix
`sys.A` holds, at every time of the horizon `[0, p.tFinal]` — `ConstTrajectory`
at `U = 0`, one matrix fixed over the whole run. The parameters are
`LinearSys.ReachParams`, the point case's: the windows `reachUnion` covers the
horizon with are how it encloses this set, not part of it.
-/

-- Authors:       Tobias Ladner
-- Written:       24-September-2026
-- Last update:   24-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix NormedSpace

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Every image of a bare initial set `X` under `exp (t • A)`, at every
`A ∈ construct sys.A` and every `t ∈ [0, p.tFinal]`. -/
noncomputable def LinParamSys.reachUnionExact (sys : LinParamSys ℐ n)
    (p : LinearSys.ReachParams) (X : Set (Vec ℝ n)) : Set (Vec ℝ n) :=
  {x | ∃ A ∈ ContSet.construct sys.A, ∃ t ∈ Set.Icc (0 : ℝ) p.tFinal,
    ∃ x₀ ∈ X, x = exp (t • A) *ᵥ x₀}

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
