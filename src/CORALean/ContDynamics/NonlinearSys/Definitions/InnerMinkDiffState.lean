module

public import CORALean.Global.Tensor
public import Mathlib.Data.Real.Basic

@[expose] public section

/-!
# What one step of the inner Minkowski-difference algorithm computes

The values lines 4-16 of [1, Alg. 1] name in one step `k`, kept so that a theorem can speak
of them: the linearization point `x*(t_k)` (`xstar`), `w` and `A` of (6), the curvature error
`C`, the constant-input solution `R_con(Δt)` (`Rcon`), the affine time-point solution
`R_aff(Δt)` (`Raff`), the enlarged remainder `L̂` (`Lhat`) the loop of lines 10-13 settles on,
the abstraction error `R̂_err(L̂)` (`Rerr`), the center `c` of line 14, and the two inner sets,
`R̂(t_{k+1})` (`Rtk1`) and `R̂(τ_k)` (`Rtauk`).

## References

* [1] M. Wetzlinger, A. Kulmburg and M. Althoff. "Inner Approximations of Reachable Sets for
      Nonlinear Systems using the Minkowski Difference". IEEE Control Systems Letters, 2024.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ========================================  MAIN TYPE  ========================================= --

/-- The values of one step of [1, Alg. 1], lines 4-16. -/
structure NonlinearSys.InnerMinkDiffState (n : ℕ) (𝓛 : Type) where
  xstar : Vec ℝ n
  w : Vec ℝ n
  A : Mat ℝ n n
  C : Set (Vec ℝ n)
  Rcon : Vec ℝ n
  Raff : Set (Vec ℝ n)
  Lhat : 𝓛
  Rerr : Set (Vec ℝ n)
  c : Vec ℝ n
  Rtk1 : Set (Vec ℝ n)
  Rtauk : Set (Vec ℝ n)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
