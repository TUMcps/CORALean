module

public import CORALean.Global.Jacobian

@[expose] public section

/-!
# What a first-order linearization leaves out

For `g : ℝⁿ × ℝᵐ → ℝᵖ` linearized at `(xs, us)`, `L(x, u)` with
`g(x, u) = g(xs, us) + A (x - xs) + B (u - us) + L(x, u)`, `A` and `B` the Jacobians at
`(xs, us)`. The linearization error of CORA's abstraction, defined here as the residual itself:
it says nothing about how small, or enclosed, that residual is.

## Inputs
* `g` – map
* `xs` – linearization state
* `us` – linearization input
* `x` – state
* `u` – input vector

## Output
* the map's value minus its first-order approximation at the linearization point
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {n m p : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `g(x,u) - g(xs,us) - A (x - xs) - B (u - us)`, `A`, `B` the Jacobians of `g` at `(xs,us)`. -/
noncomputable def linResidual (g : Vec ℝ n → Vec ℝ m → Vec ℝ p) (xs : Vec ℝ n) (us : Vec ℝ m)
    (x : Vec ℝ n) (u : Vec ℝ m) : Vec ℝ p :=
  let A := jacobianMat (fun x' => g x' us) xs                       -- ∂g/∂x at (xs, us)
  let B := jacobianMat (fun u' => g xs u') us                       -- ∂g/∂u at (xs, us)
  g x u - g xs us - A *ᵥ (x - xs) - B *ᵥ (u - us)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
