module

public import CORALean.ContDynamics.LinearSysDT.LinearSysDT

@[expose] public section

/-!
# One sampled run of the dynamics

`simulate` samples one run rather than enclosing all of them: a point
computation, carrying none of `reach`'s set instances.

## Inputs
* `sys` – system
* `x₀` – initial state
* `u` – input signal

## Output
* the state after each number of steps
-/

-- Authors:       Claude Sonnet 5
-- Written:       18-August-2026
-- Last update:   08-September-2026
-- Reviewed:      19-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Scalar

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- One sampled run of the dynamics from `x₀` under input signal `u` — a point
computation, none of `reach`'s set instances needed. -/
def LinearSysDT.simulate (sys : LinearSysDT 𝕋 n) (x₀ : Vec ℝ n) (u : ℕ → Vec ℝ n) :
    ℕ → Vec ℝ n
  | 0 => x₀
  | k + 1 => toRealMat sys.A *ᵥ sys.simulate x₀ u k + u k

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
