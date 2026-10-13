module

public import CORALean.ContDynamics.NonlinearSys.Operations.CentreAbstrRun
public import CORALean.ContDynamics.NonlinearSys.Definitions.AbstrReachOptions
public import CORALean.ContDynamics.Reach.Definitions.InputParams

@[expose] public section

/-!
# `Alg. 1` line 17, linearizing at the centre

`centreAbstrReach`: `R([0,t_K])`, the union of the first `K` iterations'
time-interval sets. Line 17's union is no zonotope, so this is a `Set`.

## References

* [1] M. Wetzlinger, A. Kulmburg and M. Althoff. "Adaptive Parameter Tuning for
      Reachability Analysis of Nonlinear Systems". HSCC, 2021, Article 16.
-/

-- Authors:       Claude Sonnet 5
-- Written:       18-September-2026
-- Last update:   30-September-2026
-- Reviewed:      ---


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

/-- [1, Alg. 1] line 17: `R([0,t_K])`, the union of the first `K` iterations'
time-interval sets. The horizon is `params.tFinal - params.tStart`, the loop's clock
starting at `0`. -/
noncomputable def NonlinearSys.centreAbstrReach (sys : NonlinearSys n m)
    (params : Reach.InputParams (S n) (S m) ℝ) (options : NonlinearSys.AbstrReachOptions S n m) :
    Set (Vec ℝ n) :=
  let X₀ := params.X₀                                               -- the paper's symbols
  let U := params.U
  let tK := params.tFinal - params.tStart
  ⋃ j < options.K, ⋃ s ∈ sys.centreAbstrRun U options.lin options.Φ options.sub options.enlarge
    options.Δt tK options.η options.taylorTermsAbstr options.ρ
    options.fuel X₀ (j + 1), construct s.Rτ

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
