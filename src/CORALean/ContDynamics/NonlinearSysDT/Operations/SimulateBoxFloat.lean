module

public import CORALean.ContDynamics.NonlinearSysDT.Definitions.FloatModel
public import CORALean.ContSet.Interval.Float.Operations.Point

@[expose] public section

/-!
# An interval-valued `simulate` for a nonlinear discrete-time system

CORA's `simulate` at a float start and a float input signal: the field's interval extension
`fm.f`, applied step by step to the box of the previous state and the point box of the input.
Soundness is `simulate_mem_simulateBoxFloat`; no rounding is claimed exact.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      14-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The float run of `simulate`: boxes containing the real run from `x₀` under `u`. -/
def NonlinearSysDT.simulateBoxFloat (fm : NonlinearSysDT.FloatModel 𝕋 n m) (x₀ : Vec 𝕋 n)
    (u : ℕ → Vec 𝕋 m) : ℕ → Interval (Vec 𝕋 n)
  | 0 => Interval.point x₀
  | k + 1 => fm.f (NonlinearSysDT.simulateBoxFloat fm x₀ u k) (Interval.point (u k))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
