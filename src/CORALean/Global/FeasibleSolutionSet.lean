module

public import CORALean.Global.Tensor
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Real.Basic

@[expose] public section

/-!
# The feasible solution set of a time-varying parameter vector

[1, Def. 1]: with the measurements `(y_k, r_k)`, `k = 1, …, N`, the error bound `σ` and the
expansion `γ`, `θ` is in the set when some `θ_1, …, θ_N` end at `θ = θ_N` (condition (i) of the
definition), meet every measurement `|y_k - r_kᵀθ_k| ≤ σ` (ii), and move by at most `γ` per step,
`‖θ_k - θ_{k-1}‖∞ ≤ γ` (iii). The expansion is a vector, one bound per parameter, as in the paper's
example; a scalar `γ` is the constant vector. The paper has no initial set: that is `Θ₀ = univ`;
the example starts from a box `Θ₀`, and `θ_1 ∈ Θ₀` is how it enters. Indices run on `ℕ`, only `1 ≤
k ≤ N` mattering.

## Inputs
* `Θ₀` – initial parameter set
* `r` – regressor vectors
* `y` – measurements
* `σ` – error bound
* `γ` – expansion per step
* `N` – number of measurements

## Output
* the parameters consistent with the measurements and the rate bounds

## References

* [1] [J. M. Bravo, T. Alamo and E. F. Camacho. "Bounded error identification of systems with
      time-varying parameters". IEEE Transactions on Automatic Control,
      2006.](../../../references/2006/bravo-tac-bounded-error-identification.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `{θ_N | θ_1 ∈ Θ₀, |y_k - r_kᵀθ_k| ≤ σ, |θ_k - θ_{k-1}| ≤ γ componentwise}`. -/
def feasibleSolutionSet (Θ₀ : Set (Vec ℝ n)) (r : ℕ → Vec ℝ n) (y : ℕ → ℝ) (σ : ℝ)
    (γ : Vec ℝ n) (N : ℕ) : Set (Vec ℝ n) :=
  {θ | ∃ θs : ℕ → Vec ℝ n, θs N = θ ∧ θs 1 ∈ Θ₀ ∧
    (∀ k, 1 ≤ k → k ≤ N → |y k - r k ⬝ᵥ θs k| ≤ σ) ∧
    (∀ k, 2 ≤ k → k ≤ N → ∀ i, |θs k i - θs (k - 1) i| ≤ γ i)}

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
