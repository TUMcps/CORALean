module

public import CORALean.ContDynamics.LinearSys.LinearSys
public import Mathlib.Analysis.Normed.Algebra.Exponential

@[expose] public section

/-!
# The exact set of the homogeneous flow at one time

The image of a bare initial set under the homogeneous flow `exp (t • A)`: the set `reachExact`
takes the union of over `[0, tFinal]`, and the set the time-point sets `timePoint` enclose at the
sample times `k Δt`.

## Inputs
* `sys` – linear system
* `t` – time
* `X₀` – initial set

## Output
* images of the initial set under the matrix exponential at the time
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Scalar NormedSpace

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The image of a bare initial set `X₀` under `exp (t • sys.A)`, the set at the one time `t`. -/
noncomputable def LinearSys.reachExactAt (sys : LinearSys 𝕋 n) (t : ℝ)
    (X₀ : Set (Vec ℝ n)) : Set (Vec ℝ n) :=
  (fun x₀ => exp (t • toRealMat sys.A) *ᵥ x₀) '' X₀

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
