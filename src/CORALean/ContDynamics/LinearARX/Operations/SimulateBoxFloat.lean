module

public import CORALean.ContDynamics.LinearARX.Operations.InputMat
public import CORALean.ContSet.Interval.Float.Instances
public import CORALean.ContSet.Interval.Float.Operations.Point
public import CORALean.ContDynamics.LinearARX.Operations.ToLinearSysDT
public import CORALean.ContDynamics.LinearSysDT.Operations.SimulateBoxIn

@[expose] public section

/-!
# An interval-valued `simulate` of the ARX model

The float counterpart of `simulate`, through the converted state-space system: the
window of `p` outputs is the state, the start window a point interval, and each
step adds `aux_feedBox`. The boxes enclose the stacked window of the real run
(`simulate_mem_simulateBox`, ruling R-SIM).

## Inputs
* `sys` – ARX system
* `y₀` – initial output window
* `u` – input signal

## Output
* boxes enclosing the output window at each step
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {dy du p : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

section
open Scalar Plus Mtimes

def LinearARX.aux_feedBox (sys : LinearARX 𝕋 dy du p) (u : ℕ → Vec 𝕋 du) (k : ℕ) :
    Interval (Vec 𝕋 (p * dy)) :=
  (List.finRange p).foldl
    (fun acc j => plus (S := Interval (Vec 𝕋 (p * dy))) acc
      (mtimes (S := ℐ𝒱[𝕋]) (sys.inputMat j.succ)
        (Interval.point (u (k + p - (j.succ : ℕ))))))
    (mtimes (S := ℐ𝒱[𝕋]) (sys.inputMat 0)
      (Interval.point (u (k + p - (0 : Fin (p + 1))))))

end


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Boxes for the window `(y(k), …, y(k+p-1))` of the run from `y₀` under `u`. -/
def LinearARX.simulateBox (sys : LinearARX 𝕋 dy du p) (y₀ : Vec 𝕋 (p * dy)) (u : ℕ → Vec 𝕋 du) :
    ℕ → Interval (Vec 𝕋 (p * dy)) :=
  sys.toLinearSysDT.simulateBoxIn (Interval.point y₀) (sys.aux_feedBox u)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
