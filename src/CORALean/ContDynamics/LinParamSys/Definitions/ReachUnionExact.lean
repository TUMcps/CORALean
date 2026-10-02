import CORALean.ContDynamics.LinParamSys.LinParamSys
import CORALean.ContSet.Interval.Real.Instances
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Topology.Instances.Matrix

/-!
# The exact set `Reach (LinParamSys ℐ)` is asked to enclose

Every image of a bare initial set under the homogeneous flow of every matrix
`sys.A` holds, at every time of the horizon `[0, tFinal]` — `ConstTrajectory`
at `U = 0`, one matrix fixed over the whole run. Positional, as the mathematics:
the windows `reachUnion` covers the horizon with are how it encloses this set,
not part of it, and `Reach` reads the horizon off `params`.
-/

-- Authors:       Tobias Ladner
-- Written:       24-September-2026
-- Last update:   30-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix NormedSpace

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Every image of a bare initial set `X` under `exp (t • A)`, at every
`A ∈ construct sys.A` and every `t ∈ [0, tFinal]`. -/
noncomputable def LinParamSys.reachUnionExact (sys : LinParamSys ℐ n)
    (tFinal : ℝ) (X : Set (Vec ℝ n)) : Set (Vec ℝ n) :=
  {x | ∃ A ∈ ContSet.construct sys.A, ∃ t ∈ Set.Icc (0 : ℝ) tFinal,
    ∃ x₀ ∈ X, x = exp (t • A) *ᵥ x₀}

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
