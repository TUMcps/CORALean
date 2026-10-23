module

public import CORALean.ContDynamics.OutputEq.OutputEq

@[expose] public section

/-!
# Output equations: the output at one state and one input

The output `y = C x + D u + k` the equation produces at one state and one input, which is what an
output set has to contain. Read into ℝ by the layer's scalar, as a trajectory is.

## Inputs
* `out` – output equation
* `x` – state at which the output is read
* `u` – input applied at that state

## Output
* the output at `x` under `u`
-/

-- Authors:       Claude Opus 5, Claude Opus 5.5
-- Written:       03-September-2026
-- Last update:   14-October-2026
-- Reviewed:      16-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Scalar

variable {n m r : ℕ} {𝕋 : Type} [Scalar 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The output at one state and one input, `C x + D u + k`. -/
def OutputEq.eval (out : OutputEq 𝕋 n m r) (x : Vec ℝ n) (u : Vec ℝ m) : Vec ℝ r :=
  toRealMat out.C *ᵥ x + toRealMat out.D *ᵥ u + toRealVec out.k

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
