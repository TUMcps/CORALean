import CORALean.ContDynamics.LinearSys.Operations.AdaptTimeStepOrder

/-!
# `Alg. 2` lines 3-12: the step-size sweep

Shrink `Δt_i` by `μ` until some order clears both bounds, the admissible
share `ε_P,max,i` (eq. 10) being recomputed at each new `Δt_i` (lines 2 and
7), being linear in `Δt_i`. The step sweep's bound is not [1]'s: its loop
shrinks `Δt_i` with no stated iteration count, so `fuel` is an argument and
the result an `Option`.

## References

* [1] M. Wetzlinger, N. Kochdumper and M. Althoff. "Adaptive parameter tuning
      for reachability analysis of linear systems". CDC, 2020, pp. 5145–5152.
-/

-- Authors:       Tobias Ladner
-- Written:       18-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Lines 3-12: shrink `Δt_i` by `μ` until some order clears both bounds, the
admissible share being recomputed at each new `Δt_i` (lines 2 and 7). -/
noncomputable def LinearSys.adaptTimeStepSearch (sys : LinearSys 𝕋 n) (le : ℝ → ℝ → Bool)
    (X₀ U : Zonotope (Vec ℝ n)) (εHmax εPmax εPacc tf ti μ : ℝ) (ηmax : ℕ) :
    ℝ → ℕ → Option (ℝ × ℕ)
  | _, 0 => none
  | Δt, k + 1 =>
    let εPi := (εPmax - εPacc) / (tf - ti) * Δt
    match LinearSys.adaptTimeStepOrder sys le X₀ U εHmax εPi Δt 2 (ηmax - 1) with
    | some η => some (Δt, η)
    | none => LinearSys.adaptTimeStepSearch sys le X₀ U εHmax εPmax εPacc tf ti μ ηmax (Δt * μ) k

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
