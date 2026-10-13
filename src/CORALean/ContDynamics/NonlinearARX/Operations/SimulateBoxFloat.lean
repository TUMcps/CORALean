import CORALean.ContDynamics.NonlinearARX.Operations.Simulate
import CORALean.ContDynamics.NonlinearARX.Operations.ToNonlinearSysDT
import CORALean.ContDynamics.NonlinearARX.Operations.FeedFloat
import CORALean.ContDynamics.NonlinearSysDT.Operations.SimulateBoxFloat

/-!
# An interval-valued `simulate` for a nonlinear ARX model

CORA's `simulate` at a float start window and a float input signal, through the converted
`NonlinearSysDT`: the float model of its field applied to the box of the stacked window and the
point box of the stacked inputs `feedFloat`. The boxes enclose the stacked window of the real run;
soundness is `simulate_mem_simulateBoxFloat`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {dy du p : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Boxes for the window `(y(k), …, y(k+p-1))` of the run from `y₀` under `u`, from a float model
of the converted system's field. -/
def NonlinearARX.simulateBoxFloat (_sys : NonlinearARX dy du p)
    (fm : NonlinearSysDT.FloatModel 𝕋 (p * dy) ((p + 1) * du)) (y₀ : Vec 𝕋 (p * dy))
    (u : ℕ → Vec 𝕋 du) : ℕ → Interval (Vec 𝕋 (p * dy)) :=
  NonlinearSysDT.simulateBoxFloat fm y₀ (NonlinearARX.feedFloat p u)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
