module

public import CORALean.ContDynamics.LinearSysDT.Instances
public import CORALean.ContDynamics.NeurNetContrSysDT.NeurNetContrSysDT
public import CORALean.ContDynamics.NeurNetContrSysDT.Operations.Basic

@[expose] public section

/-!
# One step of the closed loop at a linear plant

CORA's closed loop `aux_augmentLinear` at a `linearSysDT`, read one step at a time:
`x(k+1) = A x(k) + B [π(x(k)); u_ext(k)] + c = A x + B_nn π(x) + B_ext u_ext + c`, `E` dropped as
CORA drops it. A function of the state and the external input: the controller reads the state, so
the external input is the only thing along a run that is chosen. `IsTrajectory.linear` says that a
run with no disturbance steps by it.

## Inputs
* `sys` – closed-loop system
* `π` – controller function
* `x` – state
* `e` – external input at this step

## Output
* the next state of the closed loop
-/

-- Authors:       Claude Opus 5, Claude Opus 5.5, Claude Sonnet 5.5
-- Written:       02-September-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- One step of the closed loop at a linear plant, under the controller `π` and the external
input `e`. -/
def NeurNetContrSysDT.map (sys : NeurNetContrSysDT (LinearSysDT 𝕋 n) S n)
    (π : Vec ℝ n → Vec ℝ sys.m) (x : Vec ℝ n) (e : Vec ℝ sys.nExt) : Vec ℝ n :=
  toRealMat sys.plant.A *ᵥ x + toRealMat sys.plant.B *ᵥ sys.input (π x) e +
    toRealVec sys.plant.c

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
