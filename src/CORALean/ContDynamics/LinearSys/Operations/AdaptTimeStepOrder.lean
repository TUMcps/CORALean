import CORALean.ContDynamics.LinearSys.Operations.TimeIntervalStepCurvatureError
import CORALean.ContDynamics.LinearSys.Operations.TimePointStepRemainderError

/-!
# `Alg. 2` lines 4-5: the order sweep

Sweep the order upward from `η` while it clears both `ε_H ≤ ε_H,max` and
`ε_P ≤ ε_P,max,i`. Neither `Nat.find` nor `Classical.choose`: every decision
goes through the caller's `le`, so the float layer transcribes this with
`FloatOps.le` and it runs. The sweep's bound is [1]'s own `Φ_prop,max`.

## References

* [1] M. Wetzlinger, N. Kochdumper and M. Althoff. "Adaptive parameter tuning
      for reachability analysis of linear systems". CDC, 2020, pp. 5145–5152.
-/

-- Authors:       Claude Sonnet 5
-- Written:       18-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Lines 4-5: the coarsest order from `η` on clearing both bounds, and `none`
where the sweep reaches `Φ_prop,max` without one. -/
noncomputable def LinearSys.adaptTimeStepOrder (sys : LinearSys 𝕋 n) (le : ℝ → ℝ → Bool)
    (X₀ U : Zonotope (Vec ℝ n)) (εHmax εPi Δt : ℝ) : ℕ → ℕ → Option ℕ
  | _, 0 => none
  | η, k + 1 =>
    let εH := sys.timeIntervalStepCurvatureError Δt η X₀    -- 10. calc. HR⁺, ε_H
    let εP := sys.timePointStepRemainderError Δt η U        -- 11. calc. PR⁺, ε_P
    if (le εH εHmax && le εP εPi) = true then some η        -- 12. both inside their bounds
    else LinearSys.adaptTimeStepOrder sys le X₀ U εHmax εPi Δt (η + 1) k

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
