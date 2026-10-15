module

public import CORALean.Global.Tensor
public import Mathlib.Data.Real.Basic

@[expose] public section

/-!
# The subroutines of the inner Minkowski-difference algorithm

What [1, Alg. 1] computes by formulas of other papers or by representation-specific
routines, supplied rather than fixed: the Chebyshev center `cen` and the enclosing box `box`
(Sec. II-A, by linear programs on polytopes), the Jacobian `jac` of (6), the curvature error
`curv` of (17), `C = F(Δt) box ⊕ G(Δt) w` with the interval matrices `F` and `G` [1] cites, the
abstraction error `err` of (13), `R̂_err(L̂)`, and the Lagrange remainder `lagr` of (9) on a
domain around the linearization point. `L` and `L̂` are intervals in the paper; their type
`𝓛` is left open, with the three operations line 9-13 performs on them: the zero interval
`[0ₙ, 0ₙ]`, the scaling `μL` and the containment test `L ⊆ L̂`, a `Bool` so the loop runs.

None of the fields carries a specification: a theorem about [1, Alg. 1] states what it needs
of them as a hypothesis (`NonlinearSys.IsInnerMinkDiffCert`).

## References

* [1] M. Wetzlinger, A. Kulmburg and M. Althoff. "Inner Approximations of Reachable Sets for
  Nonlinear Systems using the Minkowski Difference". IEEE Control Systems Letters,
  8:2033-2038, 2024.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ========================================  MAIN TYPE  ========================================= --

/-- The subroutines [1, Alg. 1] takes from (6), (9), (13), (17) and Sec. II-A. -/
structure NonlinearSys.InnerMinkDiffOps (n : ℕ) (𝓛 : Type) where
  cen : Set (Vec ℝ n) → Vec ℝ n
  box : Set (Vec ℝ n) → Set (Vec ℝ n)
  jac : Vec ℝ n → Mat ℝ n n
  curv : ℝ → Mat ℝ n n → Set (Vec ℝ n) → Vec ℝ n → Set (Vec ℝ n)
  err : ℝ → Mat ℝ n n → 𝓛 → Set (Vec ℝ n)
  lagr : Vec ℝ n → Set (Vec ℝ n) → 𝓛
  zero : 𝓛
  smul : ℝ → 𝓛 → 𝓛
  sub : 𝓛 → 𝓛 → Bool

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
