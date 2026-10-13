module

public import CORALean.Global.Tensor
public import Mathlib.Data.Real.Basic

@[expose] public section

/-!
# The subroutines of CORA's inner linearized step

What CORA's `contDynamics/linReachInner.m` computes by representation-specific routines,
supplied rather than fixed: the enclosing box `interval(·)` (`box`), the emptiness test
`representsa_(·, 'emptySet', 1e-12)` (`isEmpty`, a `Bool` so the step branches), the box centre
`center(·)` (`cen`), the Jacobian of `linearize` (`jac`), the curvature error
`F * zonotope(·) + G * u` of `taylorMatrices` (`curv`), the box zonotope
`zonotope(0 * a, diag(a))` (`diagZono`), the particular solution
`particularSolution_timeVarying` (`inputSol`), and `priv_abstrerr_lin` (`abstrErr`), which
returns the true error vector `trueError` and the abstraction error set `VerrorDyn` for the
linearization point and a region. `𝓛` is the type of `VerrorDyn`, a zonotope in CORA.

None of the fields carries a specification: a theorem about the step states what it needs of
them as a hypothesis (`NonlinearSys.LinReachInnerCert`).

## References

* [1] M. Wetzlinger, A. Kulmburg and M. Althoff. "Inner Approximations of Reachable Sets for
  Nonlinear Systems using the Minkowski Difference". IEEE Control Systems Letters,
  8:2033-2038, 2024.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ========================================  MAIN TYPE  ========================================= --

/-- The subroutines CORA's `linReachInner` calls for a step of [1, Alg. 1]. -/
structure NonlinearSys.LinReachInnerOps (n : ℕ) (𝓛 : Type) where
  box : Set (Vec ℝ n) → Set (Vec ℝ n)
  isEmpty : Set (Vec ℝ n) → Bool
  cen : Set (Vec ℝ n) → Vec ℝ n
  jac : Vec ℝ n → Mat ℝ n n
  curv : ℝ → Mat ℝ n n → Set (Vec ℝ n) → Vec ℝ n → Set (Vec ℝ n)
  diagZono : Vec ℝ n → 𝓛
  inputSol : ℝ → Mat ℝ n n → 𝓛 → Set (Vec ℝ n)
  abstrErr : Vec ℝ n → Set (Vec ℝ n) → Vec ℝ n × 𝓛

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
