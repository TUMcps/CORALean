module

public import CORALean.ContDynamics.NonlinearSysDT.NonlinearSysDT

@[expose] public section

/-!
# The parameters of a general output model of a nonlinear discrete-time system

CORA's `p_GO` from `nonlinearSysDT/computeGO` [1], for the reference run `x`, `y`: `A k` and
`B k j` give `x(k+1)` from `x(0)` and the input `u(j)`, `C k` and `D k j` give `y(k)`, and `F`, `E`
the weights of the linearization errors `L = [L_x; L_y]`. Indices are `0`-based, so CORA's
`p_GO.A{k}` is `A (k - 1)`; the cells CORA leaves empty (`j > k`) are `0`. CORA materializes
`n_k` steps; here every step is defined, `n_k` being a bound on which are read.

## References

* [1] `contDynamics/@nonlinearSysDT/computeGO.m`
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ========================================  MAIN TYPE  ========================================= --

/-- The parameters of a general output model of a nonlinear discrete-time system: the reference
trajectory `x`, `y` and the Jacobian-like families `A`..`F` along it. -/
structure NonlinearSysDT.GO (n m r : ℕ) where
  x : ℕ → Vec ℝ n
  y : ℕ → Vec ℝ r
  A : ℕ → Mat ℝ n n
  B : ℕ → ℕ → Mat ℝ n m
  F : ℕ → ℕ → Mat ℝ n (n + r)
  C : ℕ → Mat ℝ r n
  D : ℕ → ℕ → Mat ℝ r m
  E : ℕ → ℕ → Mat ℝ r (n + r)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
