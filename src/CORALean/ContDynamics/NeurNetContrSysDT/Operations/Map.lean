module

public import CORALean.ContDynamics.LinearSysDT.Instances
public import CORALean.ContDynamics.NeurNetContrSysDT.NeurNetContrSysDT

@[expose] public section

/-!
# One step of the closed loop at a linear plant

CORA's closed loop `aux_augmentLinear` at a `linearSysDT`, read one step at a time:
`x(k+1) = A x(k) + B π(x(k)) + c`, `E` dropped as CORA drops it. A function: the controller
reads the state, so nothing along a run is chosen. `Trajectory.linear` says that a run with no
disturbance is its orbit.
-/

-- Authors:       Claude Opus 5, Claude Opus 5.5
-- Written:       02-September-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- One step of the closed loop at a linear plant, under the controller `π`. -/
def NeurNetContrSysDT.map (sys : NeurNetContrSysDT (LinearSysDT 𝕋 n) S n)
    (π : Vec ℝ n → Vec ℝ sys.plant.m) (x : Vec ℝ n) : Vec ℝ n :=
  toRealMat sys.plant.A *ᵥ x + toRealMat sys.plant.B *ᵥ π x + toRealVec sys.plant.c

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
