import CORALean.Global.Tensor
import Mathlib.Data.Real.Basic

/-!
# What CORA's inner linearized step computes

The values CORA's `contDynamics/linReachInner.m` names in one step of [1, Alg. 1], kept so that
a theorem can speak of them: the linearization point `p` (`options.linearizationPoint`), the
Jacobian `A`, the constant input `u = f(p)`, the curvature error `C`, the constant-input
solution `Rcon`, the time-point solution `Rlintp = e^{AΔt}(Rinit - p) + Rcon + p` of the
linearized dynamics, the region `Rmax` the abstraction error was computed on, the true error
vector `err` (`Rtp.error`), the abstraction error `VerrorDyn` and its reachable set `Rerror`,
and the two inner sets `Rtp` (`Rtp.set`) and `Rti`.

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

/-- The values of one step of CORA's `linReachInner`. -/
structure NonlinearSys.LinReachInnerState (n : ℕ) (𝓛 : Type) where
  p : Vec ℝ n
  A : Mat ℝ n n
  u : Vec ℝ n
  C : Set (Vec ℝ n)
  Rcon : Vec ℝ n
  Rlintp : Set (Vec ℝ n)
  Rmax : Set (Vec ℝ n)
  err : Vec ℝ n
  VerrorDyn : 𝓛
  Rerror : Set (Vec ℝ n)
  Rtp : Set (Vec ℝ n)
  Rti : Set (Vec ℝ n)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
