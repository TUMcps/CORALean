import CORALean.ContDynamics.NonlinearSys.Operations.AbstrRun
import CORALean.ContDynamics.NonlinearSys.Definitions.AbstrReachOptions
import CORALean.ContDynamics.Reach.Definitions.InputParams

/-!
# `Alg. 1` line 18: the reachable set

`abstrReach`: `R([0,t_end])`, the union of the first `K` iterations'
time-interval sets. Line 18 unions the steps' sets, which is no zonotope, so
this is a `Set`.

## References

* [1] M. Wetzlinger, A. Kulmburg, A. Le Penven and M. Althoff. "Adaptive
      Reachability Algorithms for Nonlinear Systems Using Abstraction Error
      Analysis". Nonlinear Analysis: Hybrid Systems, vol. 46, 2022, p. 101252.
-/

-- Authors:       Tobias Ladner
-- Written:       18-September-2026
-- Last update:   30-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet Scalar NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n m : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, LinComb (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)]
variable [∀ n, OfPoint (S n) (Vec ℝ n)] [∀ n, Recentre (S n) (Vec ℝ n)]
variable [Mtimes (Mat ℝ) S] [Mtimes ℐ S] [Real.OfInterval S]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Alg. 1] line 18: `R([0,t_end])`, the union of the first `K` iterations'
time-interval sets. The horizon is `params.tFinal - params.tStart`, the loop's clock
starting at `0`. -/
noncomputable def NonlinearSys.abstrReach (sys : NonlinearSys n m)
    (params : Reach.InputParams (S n) (S m) ℝ) (options : NonlinearSys.AbstrReachOptions S n m) :
    Set (Vec ℝ n) :=
  let X₀ := params.X₀                                               -- the paper's symbols
  let U := params.U
  let tend := params.tFinal - params.tStart
  ⋃ j < options.K, ⋃ s ∈ sys.abstrRun U options.lin options.Φ options.sub options.enlarge
    options.Δt tend options.η options.taylorTermsAbstr options.ρ
    options.fuel X₀ (j + 1), construct s.Rτ

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
