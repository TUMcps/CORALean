module

public import CORALean.Global.Tensor
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Real.Basic

@[expose] public section

/-!
# The states some input steers into the target against every disturbance

[1, Eq. 2]: for `x⁺ = Ax + Bu + Ew + K`, `X_{k+1} = {x | ∃u ∈ U, ∀w ∈ W, Ax + Bu + Ew + K
∈ X_k}`, the target reached in exactly `k` steps, the controller choosing `u` after the
state and before the disturbance. Between `backReachSetForallExact` (no control) and
`backReachSetExistsExact` (no disturbance), and neither of them: the quantifiers alternate.

The system's matrices are arguments rather than a `LinearSysDT`, which carries `A` alone;
over ℝ, with plain sets, since nothing here is computed.

## Inputs
* `A` – state matrix
* `B` – input matrix
* `E` – disturbance matrix
* `K` – offset
* `U` – input set
* `W` – disturbance set
* `X₀` – target set

## Output
* the states steered into the target robustly in `k` steps

## References

* [1] L. Yang and N. Ozay. "Scalable zonotopic under-approximation of backward
      reachable sets for uncertain linear systems". IEEE Control Systems Letters,
      6:1555-1560, 2022.
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

/-- [1, Eq. 2]: the `k`-step backward reachable set of `X₀`, robust to `W`, controlled
through `U`. -/
def LinearSysDT.backReachSetRobustExact (A : Mat ℝ n n) (B : Mat ℝ n m) (E : Mat ℝ n p)
    (K : Vec ℝ n) (U : Set (Vec ℝ m)) (W : Set (Vec ℝ p)) (X₀ : Set (Vec ℝ n)) :
    ℕ → Set (Vec ℝ n)
  | 0 => X₀
  | k + 1 => {x | ∃ u ∈ U, ∀ w ∈ W,
      A *ᵥ x + B *ᵥ u + E *ᵥ w + K ∈ LinearSysDT.backReachSetRobustExact A B E K U W X₀ k}

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
