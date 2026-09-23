import CORALean.ContDynamics.LinearSys.Operations.AdaptTimeStepSearch

/-!
# `Alg. 2`: the step size and the truncation order for one step

[1, Alg. 2] picks `Δt_i` and `Φ_prop,i`: enlarge the previous step by `1/μ`,
then run `adaptTimeStepSearch`. Line 12's connective is `∨` here; see the
`Alg. 2` finding on the reference page. `noncomputable` only because ℝ
arithmetic is.

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
