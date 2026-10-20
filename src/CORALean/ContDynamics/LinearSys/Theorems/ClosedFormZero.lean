module

public import CORALean.ContDynamics.LinearSys.Definitions.ClosedForm

@[expose] public section

/-!
# The closed form starts where it says it does

`closedForm x0 u 0 = x0`: the exponential at `0` is the identity and the
integral over a point is `0`, so the formula reduces to its own initial
point — needed wherever a run built from it has to meet `init`.

## Inputs
* `sys` – linear system
* `x0` – initial point
* `u` – input signal

## Hypotheses
* none

## Conclusion
* the closed form at time zero is the initial point
-/

-- Authors:       Claude Opus 5
-- Written:       15-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Scalar NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

/-- `closedForm` at its own starting time is the initial point it was built
from. -/
theorem LinearSys.closedForm_zero (sys : LinearSys 𝕋 n) (x0 : Vec ℝ n) (u : ℝ → Vec ℝ n) :
    sys.closedForm x0 u 0 = x0 := by
  show exp ((0:ℝ) • toRealMat sys.A) *ᵥ x0
    + ∫ s in (0:ℝ)..(0:ℝ), exp (((0:ℝ) - s) • toRealMat sys.A) *ᵥ u s = x0
  simp

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
