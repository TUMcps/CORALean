import CORALean.ContDynamics.NonlinearSys.Operations.PolyReachRun

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
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open ContSet

variable {n m o : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Alg. 1] line 18: `R([0,t_f])`, the union of the first `K` iterations' time-interval
sets. -/
noncomputable def NonlinearSys.polyReachReach (U UΔ : PolyZonotope (Vec ℝ m))
    (taylor : NonlinearSys.PolyTaylor n m o) (combine : PolyZonotope (Vec ℝ n) →
      PolyZonotope (Vec ℝ m) → PolyZonotope (Vec ℝ o)) (post : NonlinearSys.PolyPost n m o)
    (sub : PolyZonotope (Vec ℝ n) → PolyZonotope (Vec ℝ n) → Bool)
    (enlarge : PolyZonotope (Vec ℝ n) → PolyZonotope (Vec ℝ n)) (r tf : ℝ) (η fuel K : ℕ)
    (X₀ : PolyZonotope (Vec ℝ n)) : Set (Vec ℝ n) :=
  ⋃ j < K, ⋃ s ∈ NonlinearSys.polyReachRun U UΔ taylor combine post sub enlarge r tf η fuel
    X₀ (j + 1), construct s.Rτ

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
