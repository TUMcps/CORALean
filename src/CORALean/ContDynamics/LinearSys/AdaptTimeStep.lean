import CORALean.ContDynamics.LinearSys.StepConvergenceError

/-!
# `Alg. 2`: the step size and the truncation order for one step

[1, Alg. 2] picks `Δt_i` and `Φ_prop,i`: enlarge the previous step by `1/μ`,
sweep the order upward from its coarsest setting to `Φ_prop,max`, and where no
order clears both bounds shrink `Δt_i` by `μ` and sweep again. `Φ_prop` is the
truncation order `η` here, and the bounds are `ε_H ≤ ε_H,max` and
`ε_P ≤ ε_P,max,i`, the latter eq. (10)'s share of what is left of the `ε_P`
budget — recomputed at every shrink, being linear in `Δt_i`.

Neither `Nat.find` nor `Classical.choose`: every decision goes through the
caller's `le` and both sweeps are bounded recursions, so the float layer
transcribes this with `FloatOps.le` and it runs. `noncomputable` only because
ℝ arithmetic is.

The order sweep's bound is [1]'s own `Φ_prop,max`. The step sweep's is not:
[1]'s loop shrinks `Δt_i` with no stated iteration count, so `fuel` is an
argument and the result an `Option`. Line 12's connective is `∨` here; see the
`Alg. 2` finding on the reference page.

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


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Alg. 2]: the step size, the truncation order and the accumulated `ε_P`
for step `i`, or `none` where `fuel` shrinkings of `Δt_i` did not suffice. -/
noncomputable def LinearSys.adaptTimeStep (sys : LinearSys 𝕋 n) (le : ℝ → ℝ → Bool)
    (X₀ U : Zonotope (Vec ℝ n)) (εHmax εPmax εPacc tf ti Δtprev μ : ℝ) (ηmax fuel : ℕ) :
    Option (ℝ × ℕ × ℝ) :=
  let Δt := Δtprev / μ                                          -- 1. enlarge the previous step
  let sweep :=                                                  -- 2.-12. the do-while
    LinearSys.adaptTimeStepSearch sys le X₀ U εHmax εPmax εPacc tf ti μ ηmax Δt fuel
  match sweep with
  | none => none
  | some (Δti, ηi) =>                                           -- 13. accumulate, eq. (9)
    some (Δti, ηi, εPacc + sys.timePointStepRemainderError Δti ηi U)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
