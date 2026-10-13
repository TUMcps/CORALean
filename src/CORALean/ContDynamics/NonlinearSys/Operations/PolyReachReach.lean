import CORALean.ContDynamics.NonlinearSys.Operations.PolyReachRun
import CORALean.ContDynamics.NonlinearSys.Definitions.PolyReachOptions
import CORALean.ContDynamics.Reach.Definitions.InputParams

/-!
# `Alg. 1` line 18: the reachable set

`polyReachReach`: `R([0,t_f])`, the union of the first `K` iterations'
time-interval sets.

## References

* [1] M. Althoff. "Reachability Analysis of Nonlinear Systems using Conservative
      Polynomialization and Non-Convex Sets". HSCC 2013.
-/

-- Authors:       Tobias Ladner
-- Written:       21-September-2026
-- Last update:   30-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open ContSet

variable {n m o : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Alg. 1] line 18: `R([0,t_f])`, the union of the first `K` iterations' time-interval
sets. The horizon is `params.tFinal - params.tStart`, the loop's clock starting at `0`. -/
noncomputable def NonlinearSys.polyReachReach
    (params : Reach.InputParams (PolyZonotope (Vec ℝ n)) (PolyZonotope (Vec ℝ m)) ℝ)
    (options : NonlinearSys.PolyReachOptions n m o) : Set (Vec ℝ n) :=
  let X₀ := params.X₀                                               -- the paper's symbols
  let U := params.U
  let tf := params.tFinal - params.tStart
  ⋃ j < options.K, ⋃ s ∈ NonlinearSys.polyReachRun U options.UΔ options.taylor options.combine
    options.post options.sub options.enlarge options.Δt tf options.η options.fuel
    X₀ (j + 1), construct s.Rτ

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
