import CORALean.ContDynamics.NonlinearSys.Operations.PolyReachInit
import CORALean.ContDynamics.NonlinearSys.Operations.PolyReachStep

/-!
# `Alg. 1` lines 2 and 17: the loop

`polyReachRun`: [1, Alg. 1] lines 2 and 17, iterate `polyReachStep` while
`t_s < t_f`; `none` past a step that ran out of fuel.

## References

* [1] M. Althoff. "Reachability Analysis of Nonlinear Systems using Conservative
      Polynomialization and Non-Convex Sets". HSCC 2013.
-/

-- Authors:       Claude Sonnet 5
-- Written:       21-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real

variable {n m o : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Lines 2-17: iterate `polyReachStep` while `t_s < t_f`; `none` past a step that ran out
of fuel. -/
noncomputable def NonlinearSys.polyReachRun (U UΔ : PolyZonotope (Vec ℝ m))
    (taylor : NonlinearSys.PolyTaylor n m o) (combine : PolyZonotope (Vec ℝ n) →
      PolyZonotope (Vec ℝ m) → PolyZonotope (Vec ℝ o)) (post : NonlinearSys.PolyPost n m o)
    (sub : PolyZonotope (Vec ℝ n) → PolyZonotope (Vec ℝ n) → Bool)
    (enlarge : PolyZonotope (Vec ℝ n) → PolyZonotope (Vec ℝ n)) (r tf : ℝ) (η fuel : ℕ)
    (X₀ : PolyZonotope (Vec ℝ n)) : ℕ → Option (NonlinearSys.PolyReachState n)
  | 0 => some (NonlinearSys.polyReachInit X₀)                          -- 1. initialize
  | k + 1 =>
    match NonlinearSys.polyReachRun U UΔ taylor combine post sub enlarge r tf η fuel X₀ k with
    | none => none
    | some s =>
      if s.t < tf                                                     -- 2. while t_s < t_f
      then NonlinearSys.polyReachStep U UΔ taylor combine post sub enlarge r η fuel s
      else some s

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
