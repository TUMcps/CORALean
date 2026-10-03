import CORALean.ContDynamics.LinearSysDT.Operations.SimulateBoxIn
import CORALean.ContSet.Interval.Float.Operations.Point

/-!
# An interval-valued `simulate`

CORA's `simulate` at a float start and a float input signal: `simulateBoxIn` on
`Interval.point` start and inputs, every step in directed rounding. Soundness is
`simulate_mem_simulateBox`.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float

variable {n : ℕ} {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The float run of `simulate`: boxes containing the real run from `x₀` under `u`. -/
def LinearSysDT.simulateBox (sys : LinearSysDT 𝕋 n) (x₀ : Vec 𝕋 n) (u : ℕ → Vec 𝕋 n) :
    ℕ → Interval (Vec 𝕋 n) :=
  sys.simulateBoxIn (Interval.point x₀) fun k => Interval.point (u k)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
