module

public import CORALean.Global.Tensor
public import Mathlib.Analysis.Normed.Ring.Lemmas

@[expose] public section

/-!
# Def. 3: convergence order of a classical ODE solver

[1, Def. 3]: for the exact solution `ξex` of `ẋ = f(x,t)` and an approximation `ξhat`, the solver
has order `q ∈ N₀` when one constant `c`, chosen before `Δt`, `t₀` and `x₀`, bounds the local
truncation error `‖ξex(Δt;t₀,x₀) - ξhat(Δt;t₀,x₀)‖ ≤ c·Δt^(q+1)` at every step size, start time
and start point. The binder order is the whole content: a `c` chosen after `Δt` could grow with the
step, a strictly weaker statement than [1]'s. `ξex` and `ξhat` are plain functions of
`(Δt, t₀, x₀)`, not required to solve any ODE here (left to the instantiating site, as for
`HasSuperlinearDecrease`); the norm is `Vec ℝ n`'s own supremum norm, [1, Def. 3]'s `|·|`.

## Inputs
* `ξex` – exact solution as a function of step size, start time and point
* `ξhat` – approximate solution
* `q` – order

## Output
* the proposition that the approximation has this order against the exact solution

## References

* [1] M. Wetzlinger, A. Kulmburg, A. Le Penven and M. Althoff. "Adaptive
      Reachability Algorithms for Nonlinear Systems Using Abstraction Error
      Analysis". Nonlinear Analysis: Hybrid Systems, vol. 46, 2022, p. 101252.
-/

-- Authors:       Claude Opus 5
-- Written:       18-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Def. 3]: `ξhat` has convergence order `q` against the exact solution
`ξex` when one constant `c`, chosen before `Δt`, `t₀`, `x₀`, bounds the local
truncation error by `c·Δt^(q+1)` at every step size, start time and point. -/
def HasConvergenceOrder (ξex ξhat : ℝ → ℝ → Vec ℝ n → Vec ℝ n) (q : ℕ) : Prop :=
  ∃ c : ℝ, ∀ Δt : ℝ, 0 ≤ Δt → ∀ (t0 : ℝ) (x0 : Vec ℝ n),
    ‖ξex Δt t0 x0 - ξhat Δt t0 x0‖ ≤ c * Δt ^ (q + 1)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
